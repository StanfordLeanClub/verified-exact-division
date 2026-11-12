#ifndef DIV3_TIGHT_H
#define DIV3_TIGHT_H
#include "../vendor/selector/native/selector3.h"

/* Value contract: binary32 / 3 under nearest-even, gradual underflow, fused FMA,
 * and masked exceptions. Signed zeros and infinities agree; NaNs agree as a
 * class. Exception flags, traps, errno, and NaN payloads/signs are NOT preserved.
 * In particular x=3 yields 1 with an extra inexact flag. Never use fast-math.
 * Lean proves the value model, exact guard bits, and block/list control flow;
 * compiler lowering and pointer safety are checked separately, not proved.
 * src/dst must be disjoint or equal, with n accessible elements. */
static inline void div3_tight_context(efd32_t *c) {
    selector3_setup(c,3.0f);
    c->tlo=0x1.8p-101f; /* bits 0x0d400000; smallest float meeting T*lo >= 2^-126 */
}

static inline __attribute__((always_inline)) void
div3_tight_block(float *dst,const float *src,int nv) {
    __m256 x[4];
    __m256i flags=_mm256_setzero_si256();
    const __m256i k=_mm256_set1_epi32(0x7fffffff);
    const __m256i cz=_mm256_set1_epi32((int)0x9a7fffffu);
#pragma GCC unroll 4
    for(int j=0;j<nv;j++) {
        x[j]=_mm256_loadu_ps(src+8*j);
        __m256i a=_mm256_slli_epi32(_mm256_castps_si256(x[j]),1);
        flags=_mm256_or_si256(flags,_mm256_cmpgt_epi32(cz,_mm256_add_epi32(a,k)));
    }
    /* The theorem proves any flagged block needs the division arm directly.
     * There is no second range/special scan and no reload of the inputs. */
    if(__builtin_expect(!_mm256_testz_si256(flags,flags),0)) {
#pragma GCC unroll 4
        for(int j=0;j<nv;j++)
            _mm256_storeu_ps(dst+8*j,_mm256_div_ps(x[j],_mm256_set1_ps(3.0f)));
    } else {
#pragma GCC unroll 4
        for(int j=0;j<nv;j++)
            _mm256_storeu_ps(dst+8*j,_mm256_fmadd_ps(x[j],_mm256_set1_ps(0x1.555554p-2f),
                _mm256_mul_ps(x[j],_mm256_set1_ps(0x1.555556p-26f))));
    }
}

static inline void div3_tight_array(float *dst,const float *src,size_t n) {
    size_t i=0;
    /* Subtraction avoids size_t overflow in the loop bound. */
    for(;n-i>=32;i+=32) div3_tight_block(dst+i,src+i,4);
    for(;n-i>=8;i+=8) div3_tight_block(dst+i,src+i,1);
    for(;i<n;i++) {
        float x=src[i];uint32_t m=efd_bits32(x)&0x7fffffffu;
        dst[i]=(m>0 && m<0x0d400000u) ? x/3.0f : fmaf(x,0x1.555554p-2f,x*0x1.555556p-26f);
    }
}
#endif
