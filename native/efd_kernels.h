/* efd_kernels.h — AVX2+FMA kernels for array / scalar: the same value as x / y for every element, without a divide.
 * NaN in -> NaN out; the sign and payload of a NaN result are NOT guaranteed to equal those of hardware division
 * (see "NaN" below).  Built on exact_fdiv.h (per-divisor setup and scalar reference; that file is the specification).
 * Compile with -O2 -mavx2 -mfma -ffp-contract=off  (never -ffast-math).
 * (Generated from a single template for binary64 and binary32; edit both sections alike.)
 *
 * Public entry points (dst may equal src; any n; no alignment requirement):
 *   efd64_div_array(dst, src, n, y)      efd32_div_array(dst, src, n, y)        setup + default policy (EFD_P4)
 *   efd64_div_array_policy(..., policy)  efd32_div_array_policy(..., policy)    setup + chosen policy
 *   efd64_div_array_c(&c, ..., policy)   efd32_div_array_c(&c, ..., policy)     precomputed setup
 *   div64_array / div32_array            plain vdivpd / vdivps loop, same unrolling (baseline)
 *   recip64_array / recip32_array        x * (1/y), INEXACT, speed reference only
 * Modes (exact_fdiv.h): EFD_DIV -> division loop; EFD_EXACT (y a power of two) -> x * zh loop (exact for all x).
 *
 * Mode EFD_FMA.  Facts used (exact_fdiv.h header / THEOREM.md, Theorem B):
 *   F1  q = fma(x, zh, x*zl) equals x / y for every finite x with tlo <= |x| < thi.
 *   F2  if same_sign (zl and zh have the same sign) the raw q is also right for x = +-0, +-inf, NaN.
 *   F3  otherwise, for x = +-0 and +-inf, x / y is x with its sign XORed with sign(y); for +-0 the raw q is +0
 *       (fma of two zeros of opposite sign), for +-inf it is NaN (inf - inf).
 *   F4  finite nonzero x outside [tlo, thi): only real division is guaranteed.
 * Integer guard per vector (no FP compare): a = bits(x) << 1 (= 2|x| as an unsigned integer, sign dropped without a
 * mask constant); unsigned range tests are biased into signed compares:
 *   out  = (a + K)  >s C     <=> NOT (tlo <= |x| < thi)        K = 2^63 - 2Tlo, C = 2^63 + 2Thi - 2Tlo - 1
 *   spec = (a + K2) >s C2    <=> a == 0 or a >= 2 bits(inf)     K2 = 2^63 - 1,  C2 = 2^63 + 2 bits(inf) - 2
 *   tiny = Cz >s (a + K2)    <=> 1 <= a < 2Tlo  (finite nonzero |x| < tlo)       Cz = 2^63 + 2Tlo - 1
 *          [for a >= 1 the wrapped sum a + K2 read as signed is a - 1 - 2^63 and Cz read as signed is 2Tlo - 1 - 2^63,
 *           so the compare is exactly a - 1 < 2Tlo - 1.  a = 0 gives a + K2 = 2^63 - 1 = INT64_MAX, never < Cz;
 *           inf/NaN have a >= 2 bits(inf) >= 2Tlo, never flagged.  Same in 32-bit lanes with 2^31 (checked by the
 *           exhaustive binary32 test).]
 *   isinf = (a == 2 bits(inf))  (vpcmpeqq / vpcmpeqd)
 *   (Tlo, Thi = bit patterns of tlo, thi; binary32: identical with 32-bit lanes and 2^31.)
 * Blocks of EFD_UNROLL (4) vectors; the lane flags are ORed and there is ONE branch per block.  A flagged block goes
 * to an out-of-line cold slow path that reloads the block from src (nothing stored yet, so dst == src is safe): if
 * every flagged lane (w.r.t. "out") is +-0/+-inf/NaN the raw q is used with the special-lane value in those lanes
 * (F2/F3), otherwise the block is computed with real division (F4).
 * Special-lane value: x * zh.  For +-0 and +-inf this is exactly x / y (sign(zh) = sign(y)); for a NaN input x86
 * returns the quieted input NaN, which is also what vdivpd returns, so P2/P3 now reproduce NaN bits too (on x86).
 * (The former value x ^ signbit(y) flips the sign of a NaN input when y < 0; it is kept as policy EFD_P3X.)
 *
 * Policies:
 *   EFD_P1   flag "out"; flagged block -> real division.
 *   EFD_P2   flag "out"; flagged block -> slow path as above (specials without division).
 *   EFD_P3   branchless specials: q = blend(raw q, x*zh, spec) in every block (blend skipped if same_sign, F2);
 *            flag "out & ~spec" (finite nonzero lanes outside [tlo, thi), F4).
 *   EFD_P3X  P3 with special value x ^ signbit(y) (old variant, for comparison only).
 *   EFD_P4   (default) data-independent for zeros and NaN:
 *            same_sign and thi = +inf  (F1, F2): flag only "tiny"; no blend.  Zeros, infinities and NaN cost nothing.
 *            opposite sign and thi = +inf (F1, F3): zero fix instead of a blend: q |= (x & signmask) if y > 0,
 *              q |= (~x & signmask) if y < 0  (for finite nonzero in-range lanes the sign bit of q already equals
 *              sign(x) ^ sign(y), so the OR is a no-op there; for +-0 the raw +0 becomes the correctly signed zero;
 *              for NaN the result stays a NaN, its sign bit may change).  Flag "tiny | isinf": infinities (raw NaN)
 *              go to the slow path, zeros and NaN do not.
 *            finite thi (only for tiny |y|): P3.
 * Tails: single-vector blocks while >= one vector remains, then scalar efdNN_div from exact_fdiv.h.
 *
 * NaN: every policy returns a NaN exactly where x / y is NaN.  NaN bits: P1, P2, P3 and the P4 same-sign branch
 * return the quieted input NaN like vdivpd (x86 NaN propagation of mul/fma); the P4 opposite-sign branch may flip
 * the NaN's sign bit; P3X flips it when y < 0.  test_kernels.c counts NaN-bit differences separately.
 */
#ifndef EFD_KERNELS_H
#define EFD_KERNELS_H
#include <immintrin.h>
#include <stddef.h>
#include "exact_fdiv.h"

#ifndef EFD_UNROLL
#define EFD_UNROLL 4
#endif
enum { EFD_P1 = 1, EFD_P2 = 2, EFD_P3 = 3, EFD_P4 = 4, EFD_P3X = 5 };
/* internal kernel kinds (compile-time constants of the block functions) */
enum { EFD_K_P1 = 1, EFD_K_P2 = 2, EFD_K_P3 = 3, EFD_K_P3X = 5, EFD_K_Z = 6, EFD_K_ZFP = 7, EFD_K_ZFN = 8 };
#ifndef EFD_POLICY_DEFAULT
#define EFD_POLICY_DEFAULT EFD_P4
#endif

#define EFD_AI static inline __attribute__((always_inline))
#define EFD_UNLIKELY(x) __builtin_expect(!!(x), 0)

static inline uint64_t efd_bits64(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static inline uint32_t efd_bits32(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }

/* =============================================== binary64 ============================================== */
typedef struct { __m256d zh, zl, y, sgn, sm; __m256i K, C, K2, C2, Cz, INF2; } efd64_vc;

EFD_AI void efd64_vc_init(efd64_vc *v, const efd64_t *c) {
    uint64_t Tlo = efd_bits64(c->tlo), Thi = efd_bits64(c->thi), B = 0x8000000000000000ull;
    v->zh = _mm256_set1_pd(c->zh); v->zl = _mm256_set1_pd(c->zl); v->y = _mm256_set1_pd(c->y);
    v->sgn = _mm256_castsi256_pd(_mm256_set1_epi64x((long long)(efd_bits64(c->y) & B)));
    v->sm  = _mm256_castsi256_pd(_mm256_set1_epi64x((long long)B));
    v->K  = _mm256_set1_epi64x((long long)(uint64_t)(B - 2 * Tlo));
    v->C  = _mm256_set1_epi64x((long long)(uint64_t)(B + 2 * Thi - 2 * Tlo - 1));
    v->K2 = _mm256_set1_epi64x((long long)(uint64_t)(B - 1));
    v->C2 = _mm256_set1_epi64x((long long)(uint64_t)(B + 0xFFE0000000000000ull - 2));
    v->Cz = _mm256_set1_epi64x((long long)(uint64_t)(B + 2 * Tlo - 1));
    v->INF2 = _mm256_set1_epi64x((long long)0xFFE0000000000000ull);
}

/* special-lane value: x * zh (EFD_K_P3X: x ^ signbit(y)) */
#define efd64_SPV(k, xx) ((k) == EFD_K_P3X ? _mm256_xor_pd((xx), v->sgn) : _mm256_mul_pd((xx), v->zh))

/* Slow path for one flagged block of nv vectors (out of line, cold).  Reloads x from src. */
static __attribute__((noinline, cold)) void efd64_block_slow(double *dst, const double *src, const efd64_vc *v, int nv,
                                                            int k, int same) {
    __m256d x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL], r = _mm256_setzero_si256();
    for (int j = 0; j < nv; j++) {
        x[j] = _mm256_loadu_pd(src + 4 * j);
        __m256i a = _mm256_slli_epi64(_mm256_castpd_si256(x[j]), 1);
        o[j] = _mm256_cmpgt_epi64(_mm256_add_epi64(a, v->K), v->C);
        __m256i sp = _mm256_cmpgt_epi64(_mm256_add_epi64(a, v->K2), v->C2);
        r = _mm256_or_si256(r, _mm256_andnot_si256(sp, o[j]));
    }
    /* q is formed only when it is used: for tiny x, x*zl is subnormal (slow on these cores) */
    if (k != EFD_K_P1 && _mm256_testz_si256(r, r)) {      /* every flagged lane is +-0, +-inf or NaN (F2/F3) */
        for (int j = 0; j < nv; j++) {
            q[j] = _mm256_fmadd_pd(x[j], v->zh, _mm256_mul_pd(x[j], v->zl));
            if (!same) q[j] = _mm256_blendv_pd(q[j], efd64_SPV(k, x[j]), _mm256_castsi256_pd(o[j]));
        }
    } else {
        for (int j = 0; j < nv; j++) q[j] = _mm256_div_pd(x[j], v->y);       /* F4 */
    }
    for (int j = 0; j < nv; j++) _mm256_storeu_pd(dst + 4 * j, q[j]);
}

/* NV vectors (NV = EFD_UNROLL or 1) starting at src; k and same are compile-time constants */
EFD_AI void efd64_block(double *dst, const double *src, const efd64_vc *v, const int NV, const int k, const int same) {
    __m256d x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL];
    const int p3 = k == EFD_K_P3 || k == EFD_K_P3X;
    /* P3 with !same_sign forms q (and its special-lane blend) before the branch: keeping only q live across the
     * branch needs fewer registers than keeping x and spec (fewer spills).  The other kinds test first. */
    const int early = p3 && !same;
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* guard first ... */
        x[j] = _mm256_loadu_pd(src + 4 * j);
        __m256i a = _mm256_slli_epi64(_mm256_castpd_si256(x[j]), 1);
        if (k == EFD_K_P1 || k == EFD_K_P2) {
            o[j] = _mm256_cmpgt_epi64(_mm256_add_epi64(a, v->K), v->C);
        } else if (p3) {
            __m256i s = _mm256_cmpgt_epi64(_mm256_add_epi64(a, v->K2), v->C2);
            o[j] = _mm256_andnot_si256(s, _mm256_cmpgt_epi64(_mm256_add_epi64(a, v->K), v->C));   /* finite nonzero, outside [tlo, thi) */
            if (early) q[j] = _mm256_blendv_pd(_mm256_fmadd_pd(x[j], v->zh, _mm256_mul_pd(x[j], v->zl)), efd64_SPV(k, x[j]), _mm256_castsi256_pd(s));
        } else if (k == EFD_K_Z) {
            o[j] = _mm256_cmpgt_epi64(v->Cz, _mm256_add_epi64(a, v->K2));                       /* tiny only */
        } else {                                                       /* EFD_K_ZFP / EFD_K_ZFN */
            o[j] = _mm256_or_si256(_mm256_cmpgt_epi64(v->Cz, _mm256_add_epi64(a, v->K2)), _mm256_cmpeq_epi64(a, v->INF2));
        }
    }
    __m256i f = o[0];
#pragma GCC unroll 4
    for (int j = 1; j < NV; j++) f = _mm256_or_si256(f, o[j]);
    if (EFD_UNLIKELY(!_mm256_testz_si256(f, f))) { efd64_block_slow(dst, src, v, NV, k, same); return; }
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* ... then the arithmetic */
        if (!early) q[j] = _mm256_fmadd_pd(x[j], v->zh, _mm256_mul_pd(x[j], v->zl));
        if (k == EFD_K_ZFP) q[j] = _mm256_or_pd(q[j], _mm256_and_pd(x[j], v->sm));       /* y > 0: sign(q) |= sign(x) */
        if (k == EFD_K_ZFN) q[j] = _mm256_or_pd(q[j], _mm256_andnot_pd(x[j], v->sm));      /* y < 0: sign(q) |= !sign(x) */
        _mm256_storeu_pd(dst + 4 * j, q[j]);
    }
}

EFD_AI void efd64_fma_loop(const efd64_t *c, double *dst, const double *src, size_t n, const int k, const int same) {
    efd64_vc v; efd64_vc_init(&v, c);
    size_t i = 0;
    for (; i + 4 * EFD_UNROLL <= n; i += 4 * EFD_UNROLL) efd64_block(dst + i, src + i, &v, EFD_UNROLL, k, same);
    for (; i + 4 <= n; i += 4) efd64_block(dst + i, src + i, &v, 1, k, same);
    for (; i < n; i++) dst[i] = efd64_div(c, src[i]);
}

#define efd64_LOOPFN(name, k, same) \
    static void name(const efd64_t *c, double *d, const double *s, size_t n) { efd64_fma_loop(c, d, s, n, k, same); }
efd64_LOOPFN(efd64_fma_p1, EFD_K_P1, 0)
efd64_LOOPFN(efd64_fma_p2s, EFD_K_P2, 1)
efd64_LOOPFN(efd64_fma_p2d, EFD_K_P2, 0)
efd64_LOOPFN(efd64_fma_p3s, EFD_K_P3, 1)
efd64_LOOPFN(efd64_fma_p3d, EFD_K_P3, 0)
efd64_LOOPFN(efd64_fma_p3xd, EFD_K_P3X, 0)
efd64_LOOPFN(efd64_fma_z, EFD_K_Z, 1)
efd64_LOOPFN(efd64_fma_zfp, EFD_K_ZFP, 0)
efd64_LOOPFN(efd64_fma_zfn, EFD_K_ZFN, 0)

static void div64_array(double *dst, const double *src, size_t n, double y) {
    const __m256d vy = _mm256_set1_pd(y);
    size_t i = 0;
    for (; i + 4 * EFD_UNROLL <= n; i += 4 * EFD_UNROLL) {
        __m256d q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = _mm256_div_pd(_mm256_loadu_pd(src + i + 4 * j), vy);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) _mm256_storeu_pd(dst + i + 4 * j, q[j]);
    }
    for (; i + 4 <= n; i += 4) _mm256_storeu_pd(dst + i, _mm256_div_pd(_mm256_loadu_pd(src + i), vy));
    for (; i < n; i++) dst[i] = src[i] / y;
}

/* multiply by a constant: EFD_EXACT mode (m = zh, exact) and the inexact reciprocal baseline */
static void mul64_array(double *dst, const double *src, size_t n, double m) {
    const __m256d vm = _mm256_set1_pd(m);
    size_t i = 0;
    for (; i + 4 * EFD_UNROLL <= n; i += 4 * EFD_UNROLL) {
        __m256d q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = _mm256_mul_pd(_mm256_loadu_pd(src + i + 4 * j), vm);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) _mm256_storeu_pd(dst + i + 4 * j, q[j]);
    }
    for (; i + 4 <= n; i += 4) _mm256_storeu_pd(dst + i, _mm256_mul_pd(_mm256_loadu_pd(src + i), vm));
    for (; i < n; i++) dst[i] = src[i] * m;
}

static inline void recip64_array(double *dst, const double *src, size_t n, double y) { mul64_array(dst, src, n, 1.0 / y); }

static inline void efd64_div_array_c(const efd64_t *c, double *dst, const double *src, size_t n, int policy) {
    if (c->mode == EFD_EXACT) { mul64_array(dst, src, n, c->zh); return; }   /* exact for every x */
    if (c->mode != EFD_FMA) { div64_array(dst, src, n, c->y); return; }
    int thi_inf = isinf(c->thi);
    switch (policy) {
    case EFD_P1: efd64_fma_p1(c, dst, src, n); break;
    case EFD_P2: (c->same_sign ? efd64_fma_p2s : efd64_fma_p2d)(c, dst, src, n); break;
    case EFD_P3X: (c->same_sign ? efd64_fma_p3s : efd64_fma_p3xd)(c, dst, src, n); break;
    case EFD_P4:
        if (thi_inf && c->same_sign) { efd64_fma_z(c, dst, src, n); break; }
        if (thi_inf) { (signbit(c->y) ? efd64_fma_zfn : efd64_fma_zfp)(c, dst, src, n); break; }
        __attribute__((fallthrough));                  /* finite thi -> P3 */
    default: (c->same_sign ? efd64_fma_p3s : efd64_fma_p3d)(c, dst, src, n); break;
    }
}
static inline void efd64_div_array_policy(double *dst, const double *src, size_t n, double y, int policy) {
    efd64_t c; efd64_setup(&c, y); efd64_div_array_c(&c, dst, src, n, policy);
}
static inline void efd64_div_array(double *dst, const double *src, size_t n, double y) {
    efd64_div_array_policy(dst, src, n, y, EFD_POLICY_DEFAULT);
}

/* =============================================== binary32 ============================================== */
typedef struct { __m256 zh, zl, y, sgn, sm; __m256i K, C, K2, C2, Cz, INF2; } efd32_vc;

EFD_AI void efd32_vc_init(efd32_vc *v, const efd32_t *c) {
    uint32_t Tlo = efd_bits32(c->tlo), Thi = efd_bits32(c->thi), B = 0x80000000u;
    v->zh = _mm256_set1_ps(c->zh); v->zl = _mm256_set1_ps(c->zl); v->y = _mm256_set1_ps(c->y);
    v->sgn = _mm256_castsi256_ps(_mm256_set1_epi32((int)(efd_bits32(c->y) & B)));
    v->sm  = _mm256_castsi256_ps(_mm256_set1_epi32((int)B));
    v->K  = _mm256_set1_epi32((int)(uint32_t)(B - 2 * Tlo));
    v->C  = _mm256_set1_epi32((int)(uint32_t)(B + 2 * Thi - 2 * Tlo - 1));
    v->K2 = _mm256_set1_epi32((int)(uint32_t)(B - 1));
    v->C2 = _mm256_set1_epi32((int)(uint32_t)(B + 0xFF000000u - 2));
    v->Cz = _mm256_set1_epi32((int)(uint32_t)(B + 2 * Tlo - 1));
    v->INF2 = _mm256_set1_epi32((int)0xFF000000u);
}

/* special-lane value: x * zh (EFD_K_P3X: x ^ signbit(y)) */
#define efd32_SPV(k, xx) ((k) == EFD_K_P3X ? _mm256_xor_ps((xx), v->sgn) : _mm256_mul_ps((xx), v->zh))

/* Slow path for one flagged block of nv vectors (out of line, cold).  Reloads x from src. */
static __attribute__((noinline, cold)) void efd32_block_slow(float *dst, const float *src, const efd32_vc *v, int nv,
                                                            int k, int same) {
    __m256 x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL], r = _mm256_setzero_si256();
    for (int j = 0; j < nv; j++) {
        x[j] = _mm256_loadu_ps(src + 8 * j);
        __m256i a = _mm256_slli_epi32(_mm256_castps_si256(x[j]), 1);
        o[j] = _mm256_cmpgt_epi32(_mm256_add_epi32(a, v->K), v->C);
        __m256i sp = _mm256_cmpgt_epi32(_mm256_add_epi32(a, v->K2), v->C2);
        r = _mm256_or_si256(r, _mm256_andnot_si256(sp, o[j]));
    }
    /* q is formed only when it is used: for tiny x, x*zl is subnormal (slow on these cores) */
    if (k != EFD_K_P1 && _mm256_testz_si256(r, r)) {      /* every flagged lane is +-0, +-inf or NaN (F2/F3) */
        for (int j = 0; j < nv; j++) {
            q[j] = _mm256_fmadd_ps(x[j], v->zh, _mm256_mul_ps(x[j], v->zl));
            if (!same) q[j] = _mm256_blendv_ps(q[j], efd32_SPV(k, x[j]), _mm256_castsi256_ps(o[j]));
        }
    } else {
        for (int j = 0; j < nv; j++) q[j] = _mm256_div_ps(x[j], v->y);       /* F4 */
    }
    for (int j = 0; j < nv; j++) _mm256_storeu_ps(dst + 8 * j, q[j]);
}

/* NV vectors (NV = EFD_UNROLL or 1) starting at src; k and same are compile-time constants */
EFD_AI void efd32_block(float *dst, const float *src, const efd32_vc *v, const int NV, const int k, const int same) {
    __m256 x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL];
    const int p3 = k == EFD_K_P3 || k == EFD_K_P3X;
    /* P3 with !same_sign forms q (and its special-lane blend) before the branch: keeping only q live across the
     * branch needs fewer registers than keeping x and spec (fewer spills).  The other kinds test first. */
    const int early = p3 && !same;
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* guard first ... */
        x[j] = _mm256_loadu_ps(src + 8 * j);
        __m256i a = _mm256_slli_epi32(_mm256_castps_si256(x[j]), 1);
        if (k == EFD_K_P1 || k == EFD_K_P2) {
            o[j] = _mm256_cmpgt_epi32(_mm256_add_epi32(a, v->K), v->C);
        } else if (p3) {
            __m256i s = _mm256_cmpgt_epi32(_mm256_add_epi32(a, v->K2), v->C2);
            o[j] = _mm256_andnot_si256(s, _mm256_cmpgt_epi32(_mm256_add_epi32(a, v->K), v->C));   /* finite nonzero, outside [tlo, thi) */
            if (early) q[j] = _mm256_blendv_ps(_mm256_fmadd_ps(x[j], v->zh, _mm256_mul_ps(x[j], v->zl)), efd32_SPV(k, x[j]), _mm256_castsi256_ps(s));
        } else if (k == EFD_K_Z) {
            o[j] = _mm256_cmpgt_epi32(v->Cz, _mm256_add_epi32(a, v->K2));                       /* tiny only */
        } else {                                                       /* EFD_K_ZFP / EFD_K_ZFN */
            o[j] = _mm256_or_si256(_mm256_cmpgt_epi32(v->Cz, _mm256_add_epi32(a, v->K2)), _mm256_cmpeq_epi32(a, v->INF2));
        }
    }
    __m256i f = o[0];
#pragma GCC unroll 4
    for (int j = 1; j < NV; j++) f = _mm256_or_si256(f, o[j]);
    if (EFD_UNLIKELY(!_mm256_testz_si256(f, f))) { efd32_block_slow(dst, src, v, NV, k, same); return; }
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* ... then the arithmetic */
        if (!early) q[j] = _mm256_fmadd_ps(x[j], v->zh, _mm256_mul_ps(x[j], v->zl));
        if (k == EFD_K_ZFP) q[j] = _mm256_or_ps(q[j], _mm256_and_ps(x[j], v->sm));       /* y > 0: sign(q) |= sign(x) */
        if (k == EFD_K_ZFN) q[j] = _mm256_or_ps(q[j], _mm256_andnot_ps(x[j], v->sm));      /* y < 0: sign(q) |= !sign(x) */
        _mm256_storeu_ps(dst + 8 * j, q[j]);
    }
}

EFD_AI void efd32_fma_loop(const efd32_t *c, float *dst, const float *src, size_t n, const int k, const int same) {
    efd32_vc v; efd32_vc_init(&v, c);
    size_t i = 0;
    for (; i + 8 * EFD_UNROLL <= n; i += 8 * EFD_UNROLL) efd32_block(dst + i, src + i, &v, EFD_UNROLL, k, same);
    for (; i + 8 <= n; i += 8) efd32_block(dst + i, src + i, &v, 1, k, same);
    for (; i < n; i++) dst[i] = efd32_div(c, src[i]);
}

#define efd32_LOOPFN(name, k, same) \
    static void name(const efd32_t *c, float *d, const float *s, size_t n) { efd32_fma_loop(c, d, s, n, k, same); }
efd32_LOOPFN(efd32_fma_p1, EFD_K_P1, 0)
efd32_LOOPFN(efd32_fma_p2s, EFD_K_P2, 1)
efd32_LOOPFN(efd32_fma_p2d, EFD_K_P2, 0)
efd32_LOOPFN(efd32_fma_p3s, EFD_K_P3, 1)
efd32_LOOPFN(efd32_fma_p3d, EFD_K_P3, 0)
efd32_LOOPFN(efd32_fma_p3xd, EFD_K_P3X, 0)
efd32_LOOPFN(efd32_fma_z, EFD_K_Z, 1)
efd32_LOOPFN(efd32_fma_zfp, EFD_K_ZFP, 0)
efd32_LOOPFN(efd32_fma_zfn, EFD_K_ZFN, 0)

static void div32_array(float *dst, const float *src, size_t n, float y) {
    const __m256 vy = _mm256_set1_ps(y);
    size_t i = 0;
    for (; i + 8 * EFD_UNROLL <= n; i += 8 * EFD_UNROLL) {
        __m256 q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = _mm256_div_ps(_mm256_loadu_ps(src + i + 8 * j), vy);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) _mm256_storeu_ps(dst + i + 8 * j, q[j]);
    }
    for (; i + 8 <= n; i += 8) _mm256_storeu_ps(dst + i, _mm256_div_ps(_mm256_loadu_ps(src + i), vy));
    for (; i < n; i++) dst[i] = src[i] / y;
}

/* multiply by a constant: EFD_EXACT mode (m = zh, exact) and the inexact reciprocal baseline */
static void mul32_array(float *dst, const float *src, size_t n, float m) {
    const __m256 vm = _mm256_set1_ps(m);
    size_t i = 0;
    for (; i + 8 * EFD_UNROLL <= n; i += 8 * EFD_UNROLL) {
        __m256 q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = _mm256_mul_ps(_mm256_loadu_ps(src + i + 8 * j), vm);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) _mm256_storeu_ps(dst + i + 8 * j, q[j]);
    }
    for (; i + 8 <= n; i += 8) _mm256_storeu_ps(dst + i, _mm256_mul_ps(_mm256_loadu_ps(src + i), vm));
    for (; i < n; i++) dst[i] = src[i] * m;
}

static inline void recip32_array(float *dst, const float *src, size_t n, float y) { mul32_array(dst, src, n, 1.0f / y); }

static inline void efd32_div_array_c(const efd32_t *c, float *dst, const float *src, size_t n, int policy) {
    if (c->mode == EFD_EXACT) { mul32_array(dst, src, n, c->zh); return; }   /* exact for every x */
    if (c->mode != EFD_FMA) { div32_array(dst, src, n, c->y); return; }
    int thi_inf = isinf(c->thi);
    switch (policy) {
    case EFD_P1: efd32_fma_p1(c, dst, src, n); break;
    case EFD_P2: (c->same_sign ? efd32_fma_p2s : efd32_fma_p2d)(c, dst, src, n); break;
    case EFD_P3X: (c->same_sign ? efd32_fma_p3s : efd32_fma_p3xd)(c, dst, src, n); break;
    case EFD_P4:
        if (thi_inf && c->same_sign) { efd32_fma_z(c, dst, src, n); break; }
        if (thi_inf) { (signbit(c->y) ? efd32_fma_zfn : efd32_fma_zfp)(c, dst, src, n); break; }
        __attribute__((fallthrough));                  /* finite thi -> P3 */
    default: (c->same_sign ? efd32_fma_p3s : efd32_fma_p3d)(c, dst, src, n); break;
    }
}
static inline void efd32_div_array_policy(float *dst, const float *src, size_t n, float y, int policy) {
    efd32_t c; efd32_setup(&c, y); efd32_div_array_c(&c, dst, src, n, policy);
}
static inline void efd32_div_array(float *dst, const float *src, size_t n, float y) {
    efd32_div_array_policy(dst, src, n, y, EFD_POLICY_DEFAULT);
}
#endif
