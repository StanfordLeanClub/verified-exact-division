#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <immintrin.h>
#include "../vendor/selector/native/selector3.h"
#include "case_words.h"

#define NI __attribute__((noinline))
#define BARRIER() __asm__ volatile("" ::: "memory")
static float fbits(uint32_t b) { float f; memcpy(&f,&b,4); return f; }
static int nanbits(uint32_t b) { return (b&0x7fffffff)>0x7f800000u; }
static int equalbits(uint32_t a,uint32_t b) { return a==b || (nanbits(a)&&nanbits(b)); }
NI static void selected(const efd32_t *c,float *d,const float *s,size_t n) {
    efd32_div_array_c(c,d,s,n,EFD_P4);
}
NI static void reference_array(float *d,const float *s,size_t n,float y) { div32_array(d,s,n,y); }
NI static float raw(float x) { return fmaf(x,0x1.555554p-2f,x*0x1.555556p-26f); }
static uint64_t state=20261110;
static uint32_t next(void) { state^=state<<13;state^=state>>7;state^=state<<17;return (uint32_t)(state>>16); }
static void require(int p,const char *what) { if(!p) { fprintf(stderr,"FAILED: %s\n",what);exit(1); } }
static void verify(float *d,const float *ref,size_t n) {
    for(size_t i=0;i<n;i++) if(!equalbits(efd_bits32(d[i]),efd_bits32(ref[i]))) {
        fprintf(stderr,"mismatch index %zu got=%08x expected=%08x\n",i,efd_bits32(d[i]),efd_bits32(ref[i]));exit(2);
    }
}
int main(void) {
    efd32_t c; selector3_setup(&c,3.0f);
    _mm_setcsr(0x1f80);
    require(efd_bits32(c.zh)==0x3eaaaaaa && efd_bits32(c.zl)==0x32aaaaab &&
            efd_bits32(c.tlo)==0x0d800000 && efd_bits32(c.thi)==0x7f800000 &&
            c.mode==EFD_FMA && c.same_sign==1,"context constants");
    efd32_vc v; efd32_vc_init(&v,&c);
    uint32_t K[8],C[8],K2[8],C2[8],Cz[8];
    _mm256_storeu_si256((void*)K,v.K);_mm256_storeu_si256((void*)C,v.C);
    _mm256_storeu_si256((void*)K2,v.K2);_mm256_storeu_si256((void*)C2,v.C2);_mm256_storeu_si256((void*)Cz,v.Cz);
    for(int i=0;i<8;i++) require(K[i]==0x65000000 && C[i]==0x63ffffff && K2[i]==0x7fffffff && C2[i]==0x7efffffe && Cz[i]==0x9affffff,"integer guard constants");
    printf("{\"type\":\"configuration\",\"compiler\":\"%s\",\"mxcsr_controls\":%u,\"hi\":\"%08x\",\"lo\":\"%08x\",\"threshold\":\"%08x\",\"K\":\"%08x\",\"C\":\"%08x\",\"K2\":\"%08x\",\"C2\":\"%08x\",\"Cz\":\"%08x\"}\n",
        __clang_version__,_mm_getcsr()&~63u,efd_bits32(c.zh),efd_bits32(c.zl),efd_bits32(c.tlo),K[0],C[0],K2[0],C2[0],Cz[0]);
    enum {N=2048};float s[N],d[N],r[N];uint64_t comparisons=0,guard_checks=0;
    const size_t nf=sizeof fixtures/sizeof *fixtures;
    for(size_t k=0;k<nf;k++) {
        for(int i=0;i<32;i++) s[i]=fbits(fixtures[k].input);
        selected(&c,d,s,32);
        for(int i=0;i<32;i++) require(equalbits(efd_bits32(d[i]),fixtures[k].expected),fixtures[k].name);
        comparisons+=32;
        printf("{\"type\":\"fixture\",\"name\":\"%s\",\"input\":\"%08x\",\"expected\":\"%08x\",\"actual\":\"%08x\"}\n",fixtures[k].name,fixtures[k].input,fixtures[k].expected,efd_bits32(d[0]));
    }
    for(int n=0;n<=70;n++) for(size_t offset=0;offset<nf;offset++) {
        for(int i=0;i<n;i++) s[i]=fbits(fixtures[(i+offset)%nf].input);
        reference_array(r,s,n,c.y);
        selected(&c,d,s,n);verify(d,r,n);comparisons+=n;
        memcpy(d,s,n*4);selected(&c,d,d,n);verify(d,r,n);comparisons+=n;
    }
    /* Mixed-lane fallback: each possible position of one tiny lane among specials. */
    for(int tiny_lane=0;tiny_lane<32;tiny_lane++) {
        for(int i=0;i<32;i++) s[i]=fbits(fixtures[17+(i%6)].input);
        s[tiny_lane]=fbits(0x00800000);
        reference_array(r,s,32,c.y);selected(&c,d,s,32);verify(d,r,32);comparisons+=32;
    }
    for(int batch=0;batch<512;batch++) {
        for(int i=0;i<N;i++) s[i]=fbits(next());
        reference_array(r,s,N,c.y);selected(&c,d,s,N);verify(d,r,N);comparisons+=N;
        for(int i=0;i<N;i+=8) {
            __m256i bits=_mm256_loadu_si256((void*)(s+i));
            __m256i a=_mm256_slli_epi32(bits,1);
            __m256i hot=_mm256_cmpgt_epi32(v.Cz,_mm256_add_epi32(a,v.K2));
            __m256i out=_mm256_cmpgt_epi32(_mm256_add_epi32(a,v.K),v.C);
            __m256i sp=_mm256_cmpgt_epi32(_mm256_add_epi32(a,v.K2),v.C2);
            uint32_t hot_words[8],cold_words[8];
            _mm256_storeu_si256((void*)hot_words,hot);_mm256_storeu_si256((void*)cold_words,_mm256_andnot_si256(sp,out));
            for(int j=0;j<8;j++) {
                uint32_t m=efd_bits32(s[i+j])&0x7fffffffu;
                uint32_t expected=(m>0 && m<0x0d800000)?0xffffffffu:0;
                require(hot_words[j]==expected && cold_words[j]==expected,"guard/decoder correspondence");guard_checks++;
            }
        }
    }
    uint32_t raw_min=efd_bits32(raw(fbits(0x00800000)));
    require(raw_min==0x002aaaaa,"unguarded min normal counterexample");
    printf("{\"type\":\"unguarded_failure\",\"input\":\"00800000\",\"raw\":\"%08x\",\"correct\":\"002aaaab\"}\n",raw_min);
    volatile float three=3.0f;
    for(int i=0;i<32;i++) s[i]=three;
    _mm_setcsr(0x1f80);BARRIER();reference_array(r,s,32,three);BARRIER();unsigned division_flags=_mm_getcsr()&63u;
    _mm_setcsr(0x1f80);BARRIER();selected(&c,d,s,32);BARRIER();unsigned selected_flags=_mm_getcsr()&63u;
    verify(d,r,32);
    require(division_flags==0 && selected_flags==32,"inexact-flag counterexample");
    printf("{\"type\":\"flag_counterexample\",\"input\":\"40400000\",\"division_flags\":%u,\"selected_flags\":%u,\"same_values\":true}\n",division_flags,selected_flags);
    printf("{\"type\":\"result\",\"value_comparisons\":%llu,\"guard_comparisons\":%llu,\"mismatches\":0,\"nan_comparison\":\"class\"}\n",(unsigned long long)comparisons,(unsigned long long)guard_checks);
    return 0;
}
