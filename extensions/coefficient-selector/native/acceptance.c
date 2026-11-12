/* Independent value oracle: unmodified Berkeley SoftFloat 3e f32_div.
 * Expected values never use host floating-point division or the Lean model.
 * Compile this and acceptance_sut.c separately without LTO or fast-math.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include "softfloat.h"
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#endif

void acceptance_sut(float *, const float *, size_t);
void acceptance_hardware(float *, const float *, size_t);
static uint64_t comparisons, oracle_calls, array_calls, guard_page_calls;
static uint32_t bits(float x) { uint32_t b; memcpy(&b,&x,4); return b; }
static float value(uint32_t b) { float x; memcpy(&x,&b,4); return x; }
static int isnanbits(uint32_t b) { return (b&0x7fffffffU)>0x7f800000U; }
static int same(uint32_t a,uint32_t b) { return a==b || (isnanbits(a)&&isnanbits(b)); }
static void fail(const char *reason) { fprintf(stderr,"FAIL: %s\n",reason); exit(2); }
static uint32_t oracle(uint32_t a) {
    ++oracle_calls;
    return f32_div((float32_t){a},(float32_t){0x40400000U}).v;
}
static void compare(const char *where,uint32_t in,uint32_t got,uint32_t want) {
    ++comparisons;
    if (!same(got,want)) {
        fprintf(stderr,"FAIL %s input=%08x got=%08x expected=%08x\n",where,in,got,want);
        exit(2);
    }
}
static const uint32_t cases[] = {
    0,0x80000000U,1,2,3,0x80000001U,0x007fffff,0x00800000,
    0x00800001,0x013fffff,0x01400000,0x01400001,0x0d3fffff,0x0d400000,
    0x0d400001,0x0d7fffff,0x0d800000,0x0d800001,0x3f7fffff,0x3f800000,
    0x3f800001,0x403fffff,0x40400000,0x40400001,0x7f7fffff,0xff7fffffU,
    0x7f800000,0xff800000U,0x7f800001,0xff800001U,0x7fc00000,0xffffffffU
};
#define NC (sizeof cases / sizeof *cases)
#define PAD 8
#define CAP 80
/* Compare both disjoint and exact in-place use. All surrounding storage is
 * checked bitwise; every float alignment modulo one AVX vector is exercised. */
static void edges(void) {
    float src[CAP+2*PAD], dst[CAP+2*PAD]; uint32_t want[CAP], original[CAP];
    const uint32_t canary=0x4f123456U;
    for (size_t n=0;n<=70;n++) for(size_t off=0;off<8;off++)
    for (size_t phase=0;phase<NC;phase++) {
        for (size_t j=0;j<CAP+2*PAD;j++) src[j]=dst[j]=value(canary);
        for(size_t j=0;j<n;j++) {
            original[j]=cases[(j+phase)%NC]; src[PAD+off+j]=value(original[j]);
            want[j]=oracle(original[j]);
        }
        acceptance_sut(dst+PAD+off,src+PAD+off,n); ++array_calls;
        for(size_t j=0;j<n;j++) compare("disjoint",original[j],bits(dst[PAD+off+j]),want[j]);
        for(size_t j=0;j<CAP+2*PAD;j++) {
            if(j<PAD+off || j>=PAD+off+n) {
                if(bits(dst[j])!=canary || bits(src[j])!=canary) fail("array canary");
            } else if(bits(src[j])!=original[j-PAD-off]) fail("source modified");
        }
        acceptance_sut(src+PAD+off,src+PAD+off,n); ++array_calls;
        for(size_t j=0;j<n;j++) compare("in-place",original[j],bits(src[PAD+off+j]),want[j]);
        for(size_t j=0;j<CAP+2*PAD;j++)
            if((j<PAD+off || j>=PAD+off+n) && bits(src[j])!=canary) fail("in-place canary");
    }
    /* Exactly one failing raw input in every position of each block size,
     * amid ordinary values, then amid specials. Detects partial mask reductions. */
    for(size_t n=8;n<=32;n+=24) for(size_t lane=0;lane<n;lane++)
    for(int special=0;special<2;special++) {
        for(size_t j=0;j<n;j++) src[j]=value(special?cases[24+j%8]:0x40400000U);
        src[lane]=value(0x00800000);
        acceptance_sut(dst,src,n); ++array_calls;
        for(size_t j=0;j<n;j++) compare("mixed-lane",bits(src[j]),bits(dst[j]),oracle(bits(src[j])));
    }
}

/* End each accessible buffer immediately before an inaccessible page. This
 * detects vector overreads as well as overwrites, including the zero-length API.
 * It is a finite native check, not a memory-safety proof. */
static void guard_pages(void) {
    size_t page;
    char *a,*b;
#ifdef _WIN32
    SYSTEM_INFO info; GetSystemInfo(&info); page=info.dwPageSize;
    a=VirtualAlloc(NULL,2*page,MEM_RESERVE|MEM_COMMIT,PAGE_READWRITE);
    b=VirtualAlloc(NULL,2*page,MEM_RESERVE|MEM_COMMIT,PAGE_READWRITE);
    DWORD old;
    if(!a||!b||!VirtualProtect(a+page,page,PAGE_NOACCESS,&old)||
       !VirtualProtect(b+page,page,PAGE_NOACCESS,&old)) fail("guard-page allocation");
#else
    page=(size_t)sysconf(_SC_PAGESIZE);
    a=mmap(NULL,2*page,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    b=mmap(NULL,2*page,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if(a==MAP_FAILED||b==MAP_FAILED||mprotect(a+page,page,PROT_NONE)||
       mprotect(b+page,page,PROT_NONE)) fail("guard-page allocation");
#endif
    for(size_t n=0;n<=70;n++) for(size_t phase=0;phase<NC;phase++) {
        float *s=(float *)(a+page)-n,*d=(float *)(b+page)-n;
        uint32_t want[70], original[70];
        for(size_t j=0;j<n;j++) { original[j]=cases[(j+phase)%NC];s[j]=value(original[j]);want[j]=oracle(original[j]); }
        acceptance_sut(d,s,n); ++array_calls; ++guard_page_calls;
        for(size_t j=0;j<n;j++) compare("guard-page",original[j],bits(d[j]),want[j]);
        acceptance_sut(s,s,n); ++array_calls; ++guard_page_calls;
        for(size_t j=0;j<n;j++) compare("guard-page in-place",original[j],bits(s[j]),want[j]);
    }
#ifdef _WIN32
    VirtualFree(a,0,MEM_RELEASE); VirtualFree(b,0,MEM_RELEASE);
#else
    munmap(a,2*page); munmap(b,2*page);
#endif
}

/* Also exercise every encoding through the scalar tail. SIMD is checked in
 * consecutive 4096-element batches; arbitrary lane placement is covered above
 * and by the Lean reduction theorem, not by exhaustive array enumeration. */
static void sweep(uint64_t count,int exhaustive) {
    enum {N=4096}; float src[N],got[N],hw[N]; uint32_t want[N];
    uint64_t rng=UINT64_C(0x91e10da5c79e7b1d);
    for(uint64_t base=0;base<count;base+=N) {
        size_t n=(size_t)((count-base<N)?count-base:N);
        for(size_t j=0;j<n;j++) {
            rng^=rng<<13; rng^=rng>>7; rng^=rng<<17;
            uint32_t in=exhaustive?(uint32_t)(base+j):(uint32_t)rng;
            src[j]=value(in); want[j]=oracle(in);
        }
        acceptance_sut(got,src,n); acceptance_hardware(hw,src,n); ++array_calls;
        for(size_t j=0;j<n;j++) {
            uint32_t in=bits(src[j]);
            compare("SIMD/SoftFloat",in,bits(got[j]),want[j]);
            compare("hardware/SoftFloat",in,bits(hw[j]),want[j]);
            float scalar; acceptance_sut(&scalar,src+j,1); ++array_calls;
            compare("scalar/SoftFloat",in,bits(scalar),want[j]);
        }
        if(exhaustive && ((base+n)%(UINT64_C(1)<<28)==0)) {
            fprintf(stderr,"checked %llu encodings\n",(unsigned long long)(base+n)); fflush(stderr);
        }
    }
}

static void flags(void) {
    float s[32],d[32]; for(size_t i=0;i<32;i++) s[i]=value(0x40400000);
    softfloat_exceptionFlags=0;
    uint32_t expected=oracle(0x40400000); unsigned sf=softfloat_exceptionFlags;
    _mm_setcsr(0x1f80); acceptance_hardware(d,s,32); unsigned hw=_mm_getcsr()&63;
    _mm_setcsr(0x1f80); acceptance_sut(d,s,32); unsigned opt=_mm_getcsr()&63;
    if(expected!=0x3f800000 || bits(d[0])!=expected || sf!=0 || hw!=0 || opt!=32) fail("flag witness");
    printf("{\"type\":\"flags\",\"input\":\"40400000\",\"result\":\"3f800000\",\"softfloat\":%u,\"hardware\":%u,\"optimized\":%u}\n",sf,hw,opt);
}

int main(int argc,char **argv) {
    int exhaustive=argc==2 && strcmp(argv[1],"exhaustive")==0;
    if(argc>2 || (argc==2 && !exhaustive && strcmp(argv[1],"quick"))) fail("expected quick or exhaustive");
    _mm_setcsr(0x1f80);
    softfloat_roundingMode=softfloat_round_near_even;
    softfloat_detectTininess=softfloat_tininess_afterRounding;
    /* Public known answers guard against a broken oracle build or bit adapter. */
    const uint32_t inputs[]={0,0x80000000U,1,2,0x00800000,0x40400000,0x7f800000,0xff800000U};
    const uint32_t expected[]={0,0x80000000U,0,1,0x002aaaab,0x3f800000,0x7f800000,0xff800000U};
    for(size_t j=0;j<8;j++) if(oracle(inputs[j])!=expected[j]) fail("SoftFloat known answer");
    edges(); guard_pages(); flags();
    uint64_t count=exhaustive?(UINT64_C(1)<<32):(UINT64_C(1)<<20);
    sweep(count,exhaustive);
    if((_mm_getcsr()&~63U)!=0x1f80) fail("floating-point controls changed");
    printf("{\"type\":\"result\",\"mode\":\"%s\",\"sweep_inputs\":%llu,\"value_comparisons\":%llu,\"oracle_calls\":%llu,\"array_calls\":%llu,\"guard_page_calls\":%llu,\"mismatches\":0,\"nan_comparison\":\"class\"}\n",
        exhaustive?"exhaustive":"quick",(unsigned long long)count,(unsigned long long)comparisons,
        (unsigned long long)oracle_calls,(unsigned long long)array_calls,(unsigned long long)guard_page_calls);
    return 0;
}
