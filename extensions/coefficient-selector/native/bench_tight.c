#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <intrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <stdint.h>
#include <string.h>
#include "div3_tight.h"

#define NI __attribute__((noinline))
#define BARRIER() __asm__ volatile("" ::: "memory")
typedef void (*kernel_fn)(const efd32_t *, float *, const float *, size_t);
NI static void prepared(const efd32_t *c, float *d, const float *s, size_t n) {
    efd32_div_array_c(c,d,s,n,EFD_P4);
}
NI static void divide(const efd32_t *c, float *d, const float *s, size_t n) {
    div32_array(d,s,n,c->y);
}
NI static void direct(const efd32_t *c,float *d,const float *s,size_t n) {
    (void)c;div3_tight_array(d,s,n);
}
static kernel_fn funcs[5] = {prepared,prepared,prepared,direct,divide};
static const char *names[5] = {"original","selected","tight_context","tight_direct","division"};
static efd32_t contexts[5];
static uint64_t rng=UINT64_C(20261110);
static uint32_t random32(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint32_t)(rng>>16);
}
static float frombits(uint32_t u) { float f; memcpy(&f,&u,4); return f; }
static int same(float a,float b) { return efd_bits32(a)==efd_bits32(b) || (isnan(a)&&isnan(b)); }
static double freq;
static double now(void) { LARGE_INTEGER t; QueryPerformanceCounter(&t); return t.QuadPart/freq; }
static uint64_t ft(FILETIME t) { return ((uint64_t)t.dwHighDateTime<<32)|t.dwLowDateTime; }
static void system_times(const char *stage) {
    FILETIME i,k,u; GetSystemTimes(&i,&k,&u);
    printf("{\"type\":\"system_times\",\"stage\":\"%s\",\"idle\":%llu,\"kernel\":%llu,\"user\":%llu}\n",stage,
           (unsigned long long)ft(i),(unsigned long long)ft(k),(unsigned long long)ft(u));
}
static int efficiency(int cpu) {
    DWORD len=0; GetLogicalProcessorInformationEx(RelationProcessorCore,0,&len);
    char *b=malloc(len); int ec=-1;
    if(GetLogicalProcessorInformationEx(RelationProcessorCore,(void*)b,&len))
        for(DWORD off=0;off<len;) {
            PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX p=(void*)(b+off);
            for(int j=0;j<p->Processor.GroupCount;j++)
                if(p->Processor.GroupMask[j].Group==0 && (p->Processor.GroupMask[j].Mask&((KAFFINITY)1<<cpu)))
                    ec=p->Processor.EfficiencyClass;
            off+=p->Size;
        }
    free(b); return ec;
}
static void metadata(int cpu) {
    int r[4]; char brand[49]={0};
    for(int j=0;j<3;j++) { __cpuid(r,0x80000002+j); memcpy(brand+16*j,r,16); }
    printf("{\"type\":\"metadata\",\"cpu\":\"%s\",\"logical_processor\":%d,\"efficiency_class\":%d,\"mxcsr\":%u,\"compiler\":\"%s\",\"seed\":20261110}\n",
        brand,cpu,efficiency(cpu),_mm_getcsr(),__clang_version__);
    for(int i=0;i<4;i++) printf("{\"type\":\"context\",\"variant\":\"%s\",\"zh\":\"%a\",\"zl\":\"%a\",\"tlo\":\"%a\",\"thi\":\"%a\",\"mode\":%d,\"same_sign\":%d}\n",
        names[i],contexts[i].zh,contexts[i].zl,contexts[i].tlo,contexts[i].thi,contexts[i].mode,contexts[i].same_sign);
}
static const char *distributions[]={"normal","zeros10pct","inf1pct","nan1pct","tiny0.1pct","new_guard_band","tiny1pct","tiny10pct"};
static void fill(float *s,size_t n,int dist) {
    for(size_t i=0;i<n;i++) {
        uint32_t r=random32();
        uint32_t u=(r&0x807fffffu)|((97+random32()%61)<<23);
        if(dist==1 && i%10==0) u=r&0x80000000u;
        if(dist==2 && i%100==0) u=(r&0x80000000u)|0x7f800000u;
        if(dist==3 && i%100==0) u=(r&0x80000000u)|0x7fc00001u;
        if(dist==4 && i%1000==0) u=(r&0x807fffffu)|(7u<<23); /* exponent -120 */
        if(dist==5) u=(r&0x803fffffu)|0x0d400000u; /* [3*2^-102,2^-100) */
        if(dist==6 && i%100==0) u=(r&0x807fffffu)|(7u<<23);
        if(dist==7 && i%10==0) u=(r&0x807fffffu)|(7u<<23);
        s[i]=frombits(u);
    }
}
static uint64_t validate(int exhaustive) {
    enum {N=2048}; float s[N],d[N],r[N]; uint64_t checked=0;
    const uint32_t edge[]={0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x0d7fffff,
        0x0d3fffff,0x0d400000,0x0d400001,0x0e000000,0x7f7fffff,0xff7fffff,0x7f800000,
        0xff800000,0x7fc00000,0xffc00001,0x7f800001,0xff800001};
    for(int n=0;n<=70;n++) for(int shift=0;shift<19;shift++) {
        for(int i=0;i<n;i++) s[i]=frombits(edge[(i+shift)%19]);
        divide(&contexts[2],r,s,n);
        for(int v=0;v<5;v++) for(int inplace=0;inplace<2;inplace++) {
            memcpy(d,s,n*4); funcs[v](&contexts[v],d,inplace?d:s,n);
            for(int i=0;i<n;i++) if(!same(d[i],r[i])) {
                fprintf(stderr,"edge mismatch v=%d n=%d i=%d x=%08x got=%08x ref=%08x\n",v,n,i,efd_bits32(s[i]),efd_bits32(d[i]),efd_bits32(r[i])); exit(2);
            }
            checked+=n;
        }
    }
    for(int i=0;i<32;i++) s[i]=3.0f;
    for(int v=0;v<5;v++) {
        _mm_setcsr(0x1f80);BARRIER();funcs[v](&contexts[v],d,s,32);BARRIER();
        unsigned flags=_mm_getcsr()&63u;
        if(flags!=(v==4?0u:32u) || efd_bits32(d[0])!=0x3f800000u) return exit(4),0;
        printf("{\"type\":\"flag_counterexample\",\"variant\":\"%s\",\"input\":\"40400000\",\"flags\":%u,\"result\":\"3f800000\"}\n",names[v],flags);
    }
    uint64_t end=exhaustive?(UINT64_C(1)<<32):(UINT64_C(1)<<22);
    for(uint64_t base=0;base<end;base+=N) {
        for(int i=0;i<N;i++) s[i]=frombits(exhaustive?(uint32_t)(base+i):random32());
        divide(&contexts[2],r,s,N);
        for(int v=0;v<5;v++) {
            funcs[v](&contexts[v],d,s,N);
            for(int i=0;i<N;i++) if(!same(d[i],r[i])) {
                fprintf(stderr,"value mismatch v=%d x=%08x got=%08x ref=%08x\n",v,efd_bits32(s[i]),efd_bits32(d[i]),efd_bits32(r[i])); exit(2);
            }
        }
        checked+=5*N;
    }
    printf("{\"type\":\"validation\",\"exhaustive\":%s,\"distinct_bulk_inputs\":%llu,\"comparisons_including_edges\":%llu,\"mismatches\":0,\"nan_comparison\":\"class\",\"flags_compared\":false}\n",
        exhaustive?"true":"false",(unsigned long long)end,(unsigned long long)checked);
    return checked;
}
static volatile uint32_t sink;
static double trial(int v,float *d,const float *s,size_t n,size_t calls) {
    BARRIER(); double start=now();
    for(size_t j=0;j<calls;j++) { funcs[v](&contexts[v],d,s,n); BARRIER(); }
    double elapsed=now()-start; BARRIER(); sink^=efd_bits32(d[n/2]); return elapsed;
}
int main(int argc,char **argv) {
    int cpu=argc>1?atoi(argv[1]):10, reps=argc>2?atoi(argv[2]):31;
    if(!SetThreadAffinityMask(GetCurrentThread(),(DWORD_PTR)1<<cpu)) { fprintf(stderr,"pin failed\n"); return 1; }
    _mm_setcsr(0x1f80); /* RNE, gradual underflow, exception masks; flags start clear */
    LARGE_INTEGER f; QueryPerformanceFrequency(&f); freq=(double)f.QuadPart;
    efd32_setup(&contexts[0],3.0f); selector3_setup(&contexts[1],3.0f);
    div3_tight_context(&contexts[2]);contexts[3]=contexts[2];contexts[4]=contexts[0];
    metadata(cpu); system_times("start");
    if(argc>3 && !strcmp(argv[3],"exhaustive")) { validate(1); system_times("end"); return 0; }
    validate(0); fflush(stdout);
    if(argc>3 && !strcmp(argv[3],"validate")) return 0;
    const size_t sizes[]={32,256,4096,65536,1048576,16777216};
    for(int si=0;si<6;si++) for(int dist=0;dist<8;dist++) {
        size_t n=sizes[si];
        float *s=_aligned_malloc(n*4,64),*d=_aligned_malloc(n*4,64);
        if(!s||!d) return 3; fill(s,n,dist); memset(d,0,n*4);
        size_t calls=1;
        while(trial(0,d,s,n,calls)<0.0015 && calls<(1u<<24)) calls*=2;
        int nv=5;
        for(int round=-3;round<reps;round++) {
            int order[5]={0,1,2,3,4};
            for(int j=nv-1;j>0;j--) { int k=random32()%(j+1),t=order[j]; order[j]=order[k];order[k]=t; }
            for(int j=0;j<nv;j++) {
                int v=order[j]; double t=trial(v,d,s,n,calls);
                if(round>=0) printf("{\"type\":\"trial\",\"n\":%llu,\"distribution\":\"%s\",\"round\":%d,\"order\":%d,\"variant\":\"%s\",\"calls\":%llu,\"seconds\":%.12g,\"ns_per_element\":%.9g,\"processor\":%lu}\n",
                    (unsigned long long)n,distributions[dist],round,j,names[v],(unsigned long long)calls,t,t*1e9/(n*calls),GetCurrentProcessorNumber());
            }
        }
        fprintf(stderr,"cpu %d n %llu %s completed\n",cpu,(unsigned long long)n,distributions[dist]);
        fflush(stdout); _aligned_free(s);_aligned_free(d);
    }
    system_times("end"); printf("{\"type\":\"sink\",\"value\":%u}\n",sink); return 0;
}
