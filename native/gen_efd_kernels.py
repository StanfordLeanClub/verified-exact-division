#!/usr/bin/env python3
# Generates native/efd_kernels.h (binary64 and binary32 sections from one template).
import sys
out = sys.argv[1]

HEAD = r'''/* efd_kernels.h — AVX2+FMA kernels for array / scalar: the same value as x / y for every element, without a divide.
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
'''

SECTION = r'''
/* =============================================== binary@W@ ============================================== */
typedef struct { @V@ zh, zl, y, sgn, sm; __m256i K, C, K2, C2, Cz, INF2; } @P@_vc;

EFD_AI void @P@_vc_init(@P@_vc *v, const @P@_t *c) {
    @U@ Tlo = efd_bits@W@(c->tlo), Thi = efd_bits@W@(c->thi), B = @B@;
    v->zh = @SET1F@(c->zh); v->zl = @SET1F@(c->zl); v->y = @SET1F@(c->y);
    v->sgn = @CASTIF@(@SET1I@((@SI@)(efd_bits@W@(c->y) & B)));
    v->sm  = @CASTIF@(@SET1I@((@SI@)B));
    v->K  = @SET1I@((@SI@)(@U@)(B - 2 * Tlo));
    v->C  = @SET1I@((@SI@)(@U@)(B + 2 * Thi - 2 * Tlo - 1));
    v->K2 = @SET1I@((@SI@)(@U@)(B - 1));
    v->C2 = @SET1I@((@SI@)(@U@)(B + @INF2@ - 2));
    v->Cz = @SET1I@((@SI@)(@U@)(B + 2 * Tlo - 1));
    v->INF2 = @SET1I@((@SI@)@INF2@);
}

/* special-lane value: x * zh (EFD_K_P3X: x ^ signbit(y)) */
#define @P@_SPV(k, xx) ((k) == EFD_K_P3X ? @XOR@((xx), v->sgn) : @MUL@((xx), v->zh))

/* Slow path for one flagged block of nv vectors (out of line, cold).  Reloads x from src. */
static __attribute__((noinline, cold)) void @P@_block_slow(@T@ *dst, const @T@ *src, const @P@_vc *v, int nv,
                                                            int k, int same) {
    @V@ x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL], r = _mm256_setzero_si256();
    for (int j = 0; j < nv; j++) {
        x[j] = @LD@(src + @L@ * j);
        __m256i a = @SLL@(@CASTFI@(x[j]), 1);
        o[j] = @GT@(@ADD@(a, v->K), v->C);
        __m256i sp = @GT@(@ADD@(a, v->K2), v->C2);
        r = _mm256_or_si256(r, _mm256_andnot_si256(sp, o[j]));
    }
    /* q is formed only when it is used: for tiny x, x*zl is subnormal (slow on these cores) */
    if (k != EFD_K_P1 && _mm256_testz_si256(r, r)) {      /* every flagged lane is +-0, +-inf or NaN (F2/F3) */
        for (int j = 0; j < nv; j++) {
            q[j] = @FMA@(x[j], v->zh, @MUL@(x[j], v->zl));
            if (!same) q[j] = @BLEND@(q[j], @P@_SPV(k, x[j]), @CASTIF@(o[j]));
        }
    } else {
        for (int j = 0; j < nv; j++) q[j] = @DIV@(x[j], v->y);       /* F4 */
    }
    for (int j = 0; j < nv; j++) @ST@(dst + @L@ * j, q[j]);
}

/* NV vectors (NV = EFD_UNROLL or 1) starting at src; k and same are compile-time constants */
EFD_AI void @P@_block(@T@ *dst, const @T@ *src, const @P@_vc *v, const int NV, const int k, const int same) {
    @V@ x[EFD_UNROLL], q[EFD_UNROLL];
    __m256i o[EFD_UNROLL];
    const int p3 = k == EFD_K_P3 || k == EFD_K_P3X;
    /* P3 with !same_sign forms q (and its special-lane blend) before the branch: keeping only q live across the
     * branch needs fewer registers than keeping x and spec (fewer spills).  The other kinds test first. */
    const int early = p3 && !same;
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* guard first ... */
        x[j] = @LD@(src + @L@ * j);
        __m256i a = @SLL@(@CASTFI@(x[j]), 1);
        if (k == EFD_K_P1 || k == EFD_K_P2) {
            o[j] = @GT@(@ADD@(a, v->K), v->C);
        } else if (p3) {
            __m256i s = @GT@(@ADD@(a, v->K2), v->C2);
            o[j] = _mm256_andnot_si256(s, @GT@(@ADD@(a, v->K), v->C));   /* finite nonzero, outside [tlo, thi) */
            if (early) q[j] = @BLEND@(@FMA@(x[j], v->zh, @MUL@(x[j], v->zl)), @P@_SPV(k, x[j]), @CASTIF@(s));
        } else if (k == EFD_K_Z) {
            o[j] = @GT@(v->Cz, @ADD@(a, v->K2));                       /* tiny only */
        } else {                                                       /* EFD_K_ZFP / EFD_K_ZFN */
            o[j] = _mm256_or_si256(@GT@(v->Cz, @ADD@(a, v->K2)), @EQ@(a, v->INF2));
        }
    }
    __m256i f = o[0];
#pragma GCC unroll 4
    for (int j = 1; j < NV; j++) f = _mm256_or_si256(f, o[j]);
    if (EFD_UNLIKELY(!_mm256_testz_si256(f, f))) { @P@_block_slow(dst, src, v, NV, k, same); return; }
#pragma GCC unroll 4
    for (int j = 0; j < NV; j++) {                               /* ... then the arithmetic */
        if (!early) q[j] = @FMA@(x[j], v->zh, @MUL@(x[j], v->zl));
        if (k == EFD_K_ZFP) q[j] = @OR@(q[j], @AND@(x[j], v->sm));       /* y > 0: sign(q) |= sign(x) */
        if (k == EFD_K_ZFN) q[j] = @OR@(q[j], @ANDN@(x[j], v->sm));      /* y < 0: sign(q) |= !sign(x) */
        @ST@(dst + @L@ * j, q[j]);
    }
}

EFD_AI void @P@_fma_loop(const @P@_t *c, @T@ *dst, const @T@ *src, size_t n, const int k, const int same) {
    @P@_vc v; @P@_vc_init(&v, c);
    size_t i = 0;
    for (; i + @L@ * EFD_UNROLL <= n; i += @L@ * EFD_UNROLL) @P@_block(dst + i, src + i, &v, EFD_UNROLL, k, same);
    for (; i + @L@ <= n; i += @L@) @P@_block(dst + i, src + i, &v, 1, k, same);
    for (; i < n; i++) dst[i] = @P@_div(c, src[i]);
}

#define @P@_LOOPFN(name, k, same) \
    static void name(const @P@_t *c, @T@ *d, const @T@ *s, size_t n) { @P@_fma_loop(c, d, s, n, k, same); }
@P@_LOOPFN(@P@_fma_p1, EFD_K_P1, 0)
@P@_LOOPFN(@P@_fma_p2s, EFD_K_P2, 1)
@P@_LOOPFN(@P@_fma_p2d, EFD_K_P2, 0)
@P@_LOOPFN(@P@_fma_p3s, EFD_K_P3, 1)
@P@_LOOPFN(@P@_fma_p3d, EFD_K_P3, 0)
@P@_LOOPFN(@P@_fma_p3xd, EFD_K_P3X, 0)
@P@_LOOPFN(@P@_fma_z, EFD_K_Z, 1)
@P@_LOOPFN(@P@_fma_zfp, EFD_K_ZFP, 0)
@P@_LOOPFN(@P@_fma_zfn, EFD_K_ZFN, 0)

static void div@W@_array(@T@ *dst, const @T@ *src, size_t n, @T@ y) {
    const @V@ vy = @SET1F@(y);
    size_t i = 0;
    for (; i + @L@ * EFD_UNROLL <= n; i += @L@ * EFD_UNROLL) {
        @V@ q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = @DIV@(@LD@(src + i + @L@ * j), vy);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) @ST@(dst + i + @L@ * j, q[j]);
    }
    for (; i + @L@ <= n; i += @L@) @ST@(dst + i, @DIV@(@LD@(src + i), vy));
    for (; i < n; i++) dst[i] = src[i] / y;
}

/* multiply by a constant: EFD_EXACT mode (m = zh, exact) and the inexact reciprocal baseline */
static void mul@W@_array(@T@ *dst, const @T@ *src, size_t n, @T@ m) {
    const @V@ vm = @SET1F@(m);
    size_t i = 0;
    for (; i + @L@ * EFD_UNROLL <= n; i += @L@ * EFD_UNROLL) {
        @V@ q[EFD_UNROLL];
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) q[j] = @MUL@(@LD@(src + i + @L@ * j), vm);
#pragma GCC unroll 4
        for (int j = 0; j < EFD_UNROLL; j++) @ST@(dst + i + @L@ * j, q[j]);
    }
    for (; i + @L@ <= n; i += @L@) @ST@(dst + i, @MUL@(@LD@(src + i), vm));
    for (; i < n; i++) dst[i] = src[i] * m;
}

static inline void recip@W@_array(@T@ *dst, const @T@ *src, size_t n, @T@ y) { mul@W@_array(dst, src, n, @ONE@ / y); }

static inline void @P@_div_array_c(const @P@_t *c, @T@ *dst, const @T@ *src, size_t n, int policy) {
    if (c->mode == EFD_EXACT) { mul@W@_array(dst, src, n, c->zh); return; }   /* exact for every x */
    if (c->mode != EFD_FMA) { div@W@_array(dst, src, n, c->y); return; }
    int thi_inf = isinf(c->thi);
    switch (policy) {
    case EFD_P1: @P@_fma_p1(c, dst, src, n); break;
    case EFD_P2: (c->same_sign ? @P@_fma_p2s : @P@_fma_p2d)(c, dst, src, n); break;
    case EFD_P3X: (c->same_sign ? @P@_fma_p3s : @P@_fma_p3xd)(c, dst, src, n); break;
    case EFD_P4:
        if (thi_inf && c->same_sign) { @P@_fma_z(c, dst, src, n); break; }
        if (thi_inf) { (signbit(c->y) ? @P@_fma_zfn : @P@_fma_zfp)(c, dst, src, n); break; }
        __attribute__((fallthrough));                  /* finite thi -> P3 */
    default: (c->same_sign ? @P@_fma_p3s : @P@_fma_p3d)(c, dst, src, n); break;
    }
}
static inline void @P@_div_array_policy(@T@ *dst, const @T@ *src, size_t n, @T@ y, int policy) {
    @P@_t c; @P@_setup(&c, y); @P@_div_array_c(&c, dst, src, n, policy);
}
static inline void @P@_div_array(@T@ *dst, const @T@ *src, size_t n, @T@ y) {
    @P@_div_array_policy(dst, src, n, y, EFD_POLICY_DEFAULT);
}
'''

def sub(t, d):
    for k, v in d.items(): t = t.replace('@' + k + '@', v)
    assert '@' not in t.replace('@', '', 0) or True
    return t

d64 = dict(W='64', P='efd64', T='double', V='__m256d', U='uint64_t', SI='long long', B='0x8000000000000000ull',
           INF2='0xFFE0000000000000ull', SET1F='_mm256_set1_pd', SET1I='_mm256_set1_epi64x',
           CASTIF='_mm256_castsi256_pd', CASTFI='_mm256_castpd_si256', LD='_mm256_loadu_pd', ST='_mm256_storeu_pd',
           FMA='_mm256_fmadd_pd', MUL='_mm256_mul_pd', DIV='_mm256_div_pd', XOR='_mm256_xor_pd', OR='_mm256_or_pd',
           AND='_mm256_and_pd', ANDN='_mm256_andnot_pd', BLEND='_mm256_blendv_pd', SLL='_mm256_slli_epi64',
           ADD='_mm256_add_epi64', GT='_mm256_cmpgt_epi64', EQ='_mm256_cmpeq_epi64', L='4', ONE='1.0')
d32 = dict(W='32', P='efd32', T='float', V='__m256', U='uint32_t', SI='int', B='0x80000000u',
           INF2='0xFF000000u', SET1F='_mm256_set1_ps', SET1I='_mm256_set1_epi32',
           CASTIF='_mm256_castsi256_ps', CASTFI='_mm256_castps_si256', LD='_mm256_loadu_ps', ST='_mm256_storeu_ps',
           FMA='_mm256_fmadd_ps', MUL='_mm256_mul_ps', DIV='_mm256_div_ps', XOR='_mm256_xor_ps', OR='_mm256_or_ps',
           AND='_mm256_and_ps', ANDN='_mm256_andnot_ps', BLEND='_mm256_blendv_ps', SLL='_mm256_slli_epi32',
           ADD='_mm256_add_epi32', GT='_mm256_cmpgt_epi32', EQ='_mm256_cmpeq_epi32', L='8', ONE='1.0f')
s = HEAD + sub(SECTION, d64) + sub(SECTION, d32) + '#endif\n'
import re
left = re.findall(r'@[A-Z0-9]+@', s)
assert not left, left
open(out, 'w').write(s)
