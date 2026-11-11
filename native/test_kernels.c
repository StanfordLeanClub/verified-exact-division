/* Correctness of the AVX2 kernels in efd_kernels.h against scalar hardware division.
 *   part A (binary64 and binary32): structured + random divisors; arrays mixing random bit patterns, normal-range
 *          values, values straddling tlo/thi (+-1, +-2 ulp), subnormals, +-0, +-inf, NaN, max/min; densities of
 *          "special" elements 0, 1%, 10%, 50%, 100%, plus arrays that are 90% zeros / 90% NaN / 90% inf; lengths
 *          0..70 and some large ones; start offsets 0 and 1 (unaligned); out-of-place (with a canary after the end)
 *          and in-place; policies P1, P2, P3, P3X, P4, the default entry point efdNN_div_array (P4), and the
 *          divNN_array baseline.
 *   part B (binary32): ALL 2^32 bit patterns of x for >= 40 divisors, through P1, P2, P3, P4 (permuted) and P4
 *          (sequential) (chunks of 2^16, sequential order or multiplicative permutations so that specials are
 *          mixed into blocks; alternate chunks in-place).
 * Every output element is compared bitwise with scalar x / y; any NaN equals any NaN (a mismatch is a value
 * mismatch).  NaN results whose bits differ from x / y are counted separately per variant (informational).
 * Build: gcc -O2 -mavx2 -mfma -ffp-contract=off -fopenmp test_kernels.c -o test_kernels -lm
 * Usage: ./test_kernels [nrand_divisors=200] [exhaustive_f32_divisors=40] [seed=1]
 */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include "efd_kernels.h"

static uint64_t rs = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double  d_of(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static float   f_of(uint32_t b) { float f; memcpy(&f, &b, 4); return f; }
static uint64_t b_of_d(double d) { return efd_bits64(d); }
static uint32_t b_of_f(float f) { return efd_bits32(f); }
static int eq64(double a, double b) { return b_of_d(a) == b_of_d(b) || (a != a && b != b); }
static int eq32(float a, float b) { return b_of_f(a) == b_of_f(b) || (a != a && b != b); }

static long long total_cmp = 0, total_bad = 0, total_canary = 0;
static int printed = 0;
#define MAXPRINT 20

/* ------------------------------------------------ binary64 ------------------------------------------------ */
static double gen64(const efd64_t *c, int special_pct) {
    if (special_pct > 1000) {                         /* 1001/1002/1003: 90 % zeros / NaN / inf, rest as pct 10 */
        if (rnd() % 10) {
            double v = special_pct == 1001 ? 0.0 : special_pct == 1002 ? d_of(0x7FF0000000000000ull | (rnd() & 0x000FFFFFFFFFFFFFull) | 1) : INFINITY;
            return (rnd() & 1) ? -v : v;
        }
        return gen64(c, 10);
    }
    uint64_t r = rnd();
    int cls = (int)(r % 100) < special_pct ? 1 : 0;
    double v;
    if (!cls) {                                       /* "ordinary" values */
        switch ((r >> 8) % 3) {
        case 0: v = d_of((rnd() & 0x800FFFFFFFFFFFFFull) | ((uint64_t)(1023 - 60 + rnd() % 121) << 52)); break;
        case 1: v = (double)(rnd() % 256); if (v == 0) v = 1; break;   /* small integers */
        default: { v = d_of(rnd()); if (!(fabs(v) >= c->tlo && fabs(v) < c->thi) || v != v)
                       v = d_of((rnd() & 0x800FFFFFFFFFFFFFull) | (1023ull << 52)); }
        }
        return v;
    }
    switch ((r >> 8) % 12) {
    case 0: v = d_of(rnd()); break;                                    /* any bit pattern */
    case 1: { double t = c->tlo > 0 ? c->tlo : DBL_MIN; int k = (int)(rnd() % 5) - 2;
              v = t; while (k < 0) { v = nextafter(v, 0); k++; } while (k > 0) { v = nextafter(v, INFINITY); k--; } break; }
    case 2: { double t = isinf(c->thi) || c->thi == 0 ? DBL_MAX : c->thi; int k = (int)(rnd() % 5) - 2;
              v = t; while (k < 0) { v = nextafter(v, 0); k++; } while (k > 0) { v = nextafter(v, INFINITY); k--; } break; }
    case 3: v = d_of(rnd() & 0x000FFFFFFFFFFFFFull); break;            /* subnormal (or zero) */
    case 4: v = 0.0; break;
    case 5: v = INFINITY; break;
    case 6: v = d_of(0x7FF0000000000000ull | (rnd() & 0x000FFFFFFFFFFFFFull) | 1); break;   /* NaN (q or s) */
    case 7: v = DBL_MAX; break;
    case 8: v = DBL_MIN; break;
    case 9: v = 0x1p-1074; break;
    case 10: v = d_of((rnd() & 0x000FFFFFFFFFFFFFull) | ((uint64_t)(1 + rnd() % 60) << 52)); break;  /* tiny normal */
    default: v = d_of((rnd() & 0x000FFFFFFFFFFFFFull) | ((uint64_t)(2046 - rnd() % 60) << 52));    /* huge */
    }
    if (rnd() & 1) v = -v;
    return v;
}

typedef void (*k64_t)(double *, const double *, size_t, const efd64_t *, int);
static const char *pname[] = { "div", "P1", "P2", "P3", "P3X", "P4", "default" };
#define NVAR 7
static long long nanbits[2][NVAR];   /* [f64,f32][variant]: both NaN but bits differ (informational) */

static void run64(const efd64_t *c, int which, double *dst, const double *src, size_t n) {
    switch (which) {
    case 0: div64_array(dst, src, n, c->y); break;
    case 1: efd64_div_array_c(c, dst, src, n, EFD_P1); break;
    case 2: efd64_div_array_c(c, dst, src, n, EFD_P2); break;
    case 3: efd64_div_array_c(c, dst, src, n, EFD_P3); break;
    case 4: efd64_div_array_c(c, dst, src, n, EFD_P3X); break;
    case 5: efd64_div_array_c(c, dst, src, n, EFD_P4); break;
    default: efd64_div_array(dst, src, n, c->y); break;
    }
}

static void report64(const efd64_t *c, int which, int inplace, size_t n, size_t i, double x, double got, double want) {
    if (printed++ < MAXPRINT)
        printf("MISMATCH f64 %s %s n=%zu i=%zu x=0x%016llx y=0x%016llx got=0x%016llx want=0x%016llx mode=%d same=%d "
               "tlo=%a thi=%a\n", pname[which], inplace ? "inplace" : "outofplace", n, i,
               (unsigned long long)b_of_d(x), (unsigned long long)b_of_d(c->y), (unsigned long long)b_of_d(got),
               (unsigned long long)b_of_d(want), c->mode, c->same_sign, c->tlo, c->thi);
}

static void test_divisor64(double y, long long *mode_hist) {
    efd64_t c; efd64_setup(&c, y);
    mode_hist[c.mode]++;
    static const size_t big[] = { 255, 256, 257, 1000, 4096 + 13, 65536 + 7 };
    const size_t NB = 65536 + 7 + 8;
    double *src = malloc(NB * 8), *want = malloc(NB * 8), *dst = malloc((NB + 8) * 8), *tmp = malloc(NB * 8);
    static const int dens[] = { 0, 1, 10, 50, 100, 1001, 1002, 1003 };
    for (int di = 0; di < 8; di++) {
        for (size_t i = 0; i < NB; i++) { src[i] = gen64(&c, dens[di]); want[i] = src[i] / y; }
        for (int li = 0; li < 71 + 6; li++) {
            size_t n = li < 71 ? (size_t)li : big[li - 71];
            for (int off = 0; off < 2; off++)
                for (int w = 0; w < NVAR; w++) {
                    /* out of place with canary */
                    for (size_t i = 0; i < n + 8; i++) dst[i] = d_of(0x7FF4DEADBEEF0000ull + i);
                    run64(&c, w, dst, src + off, n);
                    for (size_t i = 0; i < n; i++) {
                        total_cmp++;
                        if (dst[i] != dst[i] && b_of_d(dst[i]) != b_of_d(want[off + i])) nanbits[0][w]++;
                        if (!eq64(dst[i], want[off + i])) { total_bad++; report64(&c, w, 0, n, i, src[off + i], dst[i], want[off + i]); }
                    }
                    for (size_t i = n; i < n + 8; i++) if (b_of_d(dst[i]) != 0x7FF4DEADBEEF0000ull + i) total_canary++;
                    /* in place */
                    memcpy(tmp, src, (n + off) * 8);
                    run64(&c, w, tmp + off, tmp + off, n);
                    for (size_t i = 0; i < n; i++) {
                        total_cmp++;
                        if (tmp[off + i] != tmp[off + i] && b_of_d(tmp[off + i]) != b_of_d(want[off + i])) nanbits[0][w]++;
                        if (!eq64(tmp[off + i], want[off + i])) { total_bad++; report64(&c, w, 1, n, i, src[off + i], tmp[off + i], want[off + i]); }
                    }
                }
        }
    }
    free(src); free(want); free(dst); free(tmp);
}

/* ------------------------------------------------ binary32 ------------------------------------------------ */
static float gen32(const efd32_t *c, int special_pct) {
    if (special_pct > 1000) {
        if (rnd() % 10) {
            float v = special_pct == 1001 ? 0.0f : special_pct == 1002 ? f_of(0x7F800000u | ((uint32_t)rnd() & 0x007FFFFFu) | 1) : INFINITY;
            return (rnd() & 1) ? -v : v;
        }
        return gen32(c, 10);
    }
    uint64_t r = rnd();
    float v;
    if ((int)(r % 100) >= special_pct) {
        switch ((r >> 8) % 3) {
        case 0: v = f_of(((uint32_t)rnd() & 0x807FFFFFu) | ((uint32_t)(127 - 30 + rnd() % 61) << 23)); break;
        case 1: v = (float)(rnd() % 256); if (v == 0) v = 1; break;
        default: { v = f_of((uint32_t)rnd()); if (!(fabsf(v) >= c->tlo && fabsf(v) < c->thi) || v != v)
                       v = f_of(((uint32_t)rnd() & 0x807FFFFFu) | (127u << 23)); }
        }
        return v;
    }
    switch ((r >> 8) % 12) {
    case 0: v = f_of((uint32_t)rnd()); break;
    case 1: { float t = c->tlo > 0 ? c->tlo : FLT_MIN; int k = (int)(rnd() % 5) - 2;
              v = t; while (k < 0) { v = nextafterf(v, 0); k++; } while (k > 0) { v = nextafterf(v, INFINITY); k--; } break; }
    case 2: { float t = isinf(c->thi) || c->thi == 0 ? FLT_MAX : c->thi; int k = (int)(rnd() % 5) - 2;
              v = t; while (k < 0) { v = nextafterf(v, 0); k++; } while (k > 0) { v = nextafterf(v, INFINITY); k--; } break; }
    case 3: v = f_of((uint32_t)rnd() & 0x007FFFFFu); break;
    case 4: v = 0.0f; break;
    case 5: v = INFINITY; break;
    case 6: v = f_of(0x7F800000u | ((uint32_t)rnd() & 0x007FFFFFu) | 1); break;
    case 7: v = FLT_MAX; break;
    case 8: v = FLT_MIN; break;
    case 9: v = 0x1p-149f; break;
    case 10: v = f_of(((uint32_t)rnd() & 0x007FFFFFu) | ((uint32_t)(1 + rnd() % 30) << 23)); break;
    default: v = f_of(((uint32_t)rnd() & 0x007FFFFFu) | ((uint32_t)(254 - rnd() % 30) << 23));
    }
    if (rnd() & 1) v = -v;
    return v;
}

static void run32(const efd32_t *c, int which, float *dst, const float *src, size_t n) {
    switch (which) {
    case 0: div32_array(dst, src, n, c->y); break;
    case 1: efd32_div_array_c(c, dst, src, n, EFD_P1); break;
    case 2: efd32_div_array_c(c, dst, src, n, EFD_P2); break;
    case 3: efd32_div_array_c(c, dst, src, n, EFD_P3); break;
    case 4: efd32_div_array_c(c, dst, src, n, EFD_P3X); break;
    case 5: efd32_div_array_c(c, dst, src, n, EFD_P4); break;
    default: efd32_div_array(dst, src, n, c->y); break;
    }
}

static void report32(const efd32_t *c, const char *what, int inplace, size_t n, size_t i, float x, float got, float want) {
    int k;
    #pragma omp atomic capture
    k = printed++;
    if (k < MAXPRINT)
        printf("MISMATCH f32 %s %s n=%zu i=%zu x=0x%08x y=0x%08x got=0x%08x want=0x%08x mode=%d same=%d tlo=%a thi=%a\n",
               what, inplace ? "inplace" : "outofplace", n, i, b_of_f(x), b_of_f(c->y), b_of_f(got), b_of_f(want),
               c->mode, c->same_sign, (double)c->tlo, (double)c->thi);
}

static void test_divisor32(float y, long long *mode_hist) {
    efd32_t c; efd32_setup(&c, y);
    mode_hist[c.mode]++;
    static const size_t big[] = { 255, 256, 257, 1000, 4096 + 13, 65536 + 7 };
    const size_t NB = 65536 + 7 + 8;
    float *src = malloc(NB * 4), *want = malloc(NB * 4), *dst = malloc((NB + 8) * 4), *tmp = malloc(NB * 4);
    static const int dens[] = { 0, 1, 10, 50, 100, 1001, 1002, 1003 };
    for (int di = 0; di < 8; di++) {
        for (size_t i = 0; i < NB; i++) { src[i] = gen32(&c, dens[di]); want[i] = src[i] / y; }
        for (int li = 0; li < 71 + 6; li++) {
            size_t n = li < 71 ? (size_t)li : big[li - 71];
            for (int off = 0; off < 2; off++)
                for (int w = 0; w < NVAR; w++) {
                    for (size_t i = 0; i < n + 8; i++) dst[i] = f_of(0x7FA00000u + (uint32_t)i);
                    run32(&c, w, dst, src + off, n);
                    for (size_t i = 0; i < n; i++) {
                        total_cmp++;
                        if (dst[i] != dst[i] && b_of_f(dst[i]) != b_of_f(want[off + i])) nanbits[1][w]++;
                        if (!eq32(dst[i], want[off + i])) { total_bad++; report32(&c, pname[w], 0, n, i, src[off + i], dst[i], want[off + i]); }
                    }
                    for (size_t i = n; i < n + 8; i++) if (b_of_f(dst[i]) != 0x7FA00000u + (uint32_t)i) total_canary++;
                    memcpy(tmp, src, (n + off) * 4);
                    run32(&c, w, tmp + off, tmp + off, n);
                    for (size_t i = 0; i < n; i++) {
                        total_cmp++;
                        if (tmp[off + i] != tmp[off + i] && b_of_f(tmp[off + i]) != b_of_f(want[off + i])) nanbits[1][w]++;
                        if (!eq32(tmp[off + i], want[off + i])) { total_bad++; report32(&c, pname[w], 1, n, i, src[off + i], tmp[off + i], want[off + i]); }
                    }
                }
        }
    }
    free(src); free(want); free(dst); free(tmp);
}

/* part B: all 2^32 x for one binary32 divisor; returns mismatches, adds comparisons to *cmp */
#define NPB 5
static long long exhaustive32(float y, long long *cmp) {
    efd32_t c; efd32_setup(&c, y);
    static const uint32_t mult[NPB] = { 1u, 0x9E3779B1u, 0x85EBCA6Bu, 0xC2B2AE35u, 1u };   /* odd => bijection */
    static const int pol[NPB] = { EFD_P1, EFD_P2, EFD_P3, EFD_P4, EFD_P4 };   /* P4 twice: permuted and sequential */
    static const int pidx[NPB] = { 1, 2, 3, 5, 5 };
    long long bad = 0, ncmp = 0;
    const int CH = 1 << 16;
    #pragma omp parallel reduction(+:bad,ncmp)
    {
        float *x = malloc(CH * 4), *want = malloc(CH * 4), *got = malloc(CH * 4);
        #pragma omp for schedule(dynamic, 64)
        for (long long ch = 0; ch < (1LL << 16); ch++) {
            for (int p = 0; p < NPB; p++) {
                for (int i = 0; i < CH; i++) x[i] = f_of((uint32_t)((uint32_t)(ch * CH + i) * mult[p]));
                for (int i = 0; i < CH; i++) want[i] = x[i] / y;
                int inplace = (int)((ch + p) & 1);
                if (inplace) { memcpy(got, x, CH * 4); efd32_div_array_c(&c, got, got, CH, pol[p]); }
                else efd32_div_array_c(&c, got, x, CH, pol[p]);
                for (int i = 0; i < CH; i++)
                    if (!eq32(got[i], want[i])) { bad++; report32(&c, pname[pidx[p]], inplace, CH, i, x[i], got[i], want[i]); }
                ncmp += CH;
            }
        }
        free(x); free(want); free(got);
    }
    *cmp += ncmp;
    printf("exhaustive f32 y=%-14.9g (0x%08x) mode=%d same=%d tlo=%-12.6g thi=%-12.6g mismatches=%lld\n",
           y, b_of_f(y), c.mode, c.same_sign, c.tlo, c.thi, bad);
    fflush(stdout);
    return bad;
}

int main(int argc, char **argv) {
    int nrand = argc > 1 ? atoi(argv[1]) : 200;
    int nexh = argc > 2 ? atoi(argv[2]) : 40;
    rs = argc > 3 ? strtoull(argv[3], 0, 0) * 0x9E3779B97F4A7C15ull + 1 : 0x9E3779B97F4A7C15ull;

    /* ---- part A, binary64 ---- */
    static const double fixed64[] = { 3, 10, 255, 1000, 0.1, 1e-3, 3.141592653589793, 2.718281828459045,
        1.7320508075688772, 7, 9, 11, 49, 360, 1e6, 1e9, 1e15, 9007199254740991.0, 4503599627370497.0, 0.3,
        1, 2, 0.5, 4, 1024, 0x1p-1022, 0x1p-1021, 0x1p1023, 0x1p-1000, 0x1p1000, 0x1p-1020, 0x1p1022,
        DBL_MIN, 3 * DBL_MIN, 1.5 * 0x1p-1022, 1e-307, 1e-300, 1e-200, 1e-100, 1e100, 1e200, 1e300, 1e307, 1e308,
        DBL_MAX, 0x1.fffffffffffffp1022, 0x1.0000000000001p1023, 3 * 0x1p1021, 0x1.5555555555555p-1022,
        0x1.0000000000001p0, 0x1.fffffffffffffp0, 0x1.fffffffffffffp-1, 0x1.0000000000001p-1022,
        1e-310, 0x1p-1074, 0.0, INFINITY, NAN, 0x1.8p-1023 };
    int nf64 = sizeof fixed64 / sizeof fixed64[0];
    long long mh64[3] = { 0, 0, 0 }, mh32[3] = { 0, 0, 0 };
    int nd64 = 0, nd32 = 0;
    for (int i = 0; i < 2 * nf64 + 2 * nrand; i++) {
        double y;
        if (i < 2 * nf64) y = (i & 1) ? -fixed64[i / 2] : fixed64[i / 2];
        else if (i < 2 * nf64 + nrand) y = d_of(rnd());
        else y = d_of((rnd() & 0x800FFFFFFFFFFFFFull) | ((uint64_t)(1023 - 40 + rnd() % 81) << 52));
        test_divisor64(y, mh64); nd64++;
    }
    long long cmp64 = total_cmp, bad64 = total_bad;
    printf("part A f64: divisors=%d (DIV=%lld EXACT=%lld FMA=%lld) elements compared=%lld mismatches=%lld canary=%lld\n",
           nd64, mh64[0], mh64[1], mh64[2], cmp64, bad64, total_canary);
    fflush(stdout);

    /* ---- part A, binary32 ---- */
    static const float fixed32[] = { 3, 10, 255, 1000, 0.1f, 1e-3f, 3.14159274f, 2.71828175f, 1.73205081f, 7, 9,
        11, 49, 360, 1e6f, 16777215.0f, 8388609.0f, 0.3f, 1, 2, 0.5f, 1024, 0x1p-126f, 0x1p-125f, 0x1p127f, 0x1p-100f,
        0x1p100f, FLT_MIN, 3 * FLT_MIN, 1.2e-38f, 2e-38f, 1e-36f, 1e-30f, 1e30f, 1e36f, 3e38f, FLT_MAX,
        0x1.fffffep126f, 0x1.000002p127f, 1.00000012f, 1.99999988f, 0.99999994f, 4.7e-38f, 1e-40f, 1e-45f, 0.0f,
        INFINITY, NAN, 9.80665f, 6.28318548f, 255.5f };
    int nf32 = sizeof fixed32 / sizeof fixed32[0];
    for (int i = 0; i < 2 * nf32 + 2 * nrand; i++) {
        float y;
        if (i < 2 * nf32) y = (i & 1) ? -fixed32[i / 2] : fixed32[i / 2];
        else if (i < 2 * nf32 + nrand) y = f_of((uint32_t)rnd());
        else y = f_of(((uint32_t)rnd() & 0x807FFFFFu) | ((uint32_t)(127 - 20 + rnd() % 41) << 23));
        test_divisor32(y, mh32); nd32++;
    }
    long long cmp32 = total_cmp - cmp64, bad32 = total_bad - bad64;
    printf("part A f32: divisors=%d (DIV=%lld EXACT=%lld FMA=%lld) elements compared=%lld mismatches=%lld canary=%lld\n",
           nd32, mh32[0], mh32[1], mh32[2], cmp32, bad32, total_canary);
    fflush(stdout);

    /* ---- part B, binary32 exhaustive ---- */
    static const float exh[] = { 3, -3, 10, 255, -255, 1000, 0.1f, 1e-3f, 3.14159274f, 1.73205081f, 7, 49, 360,
        16777215.0f, 8388609.0f, 0.3f, 2, 0x1p-126f, 3e38f, -3e38f, 1.2e-38f, 2e-38f, 1e-36f, 1e-30f, 1e30f,
        FLT_MAX, FLT_MIN, 3 * FLT_MIN, 1.99999988f, 1.00000012f, 9.80665f, 6.28318548f,
        -0.1f, -1e-3f, -1e-30f, -1e-36f, -2e-38f, -7, -1000, -1.73205081f };
    int nfixed_exh = sizeof exh / sizeof exh[0];
    long long cmpB = 0, badB = 0; int ndB = 0, nfmaB = 0, nsameB = 0;
    int ntotB = nexh <= 0 ? 0 : (nexh > nfixed_exh ? nexh : nfixed_exh);
    for (int i = 0; i < ntotB; i++) {
        float y;
        if (i < nfixed_exh) y = exh[i];
        else if (i & 1) y = f_of((uint32_t)rnd());
        else y = f_of(((uint32_t)rnd() & 0x807FFFFFu) | ((uint32_t)(127 - 20 + rnd() % 41) << 23));
        efd32_t c; efd32_setup(&c, y); nfmaB += c.mode == EFD_FMA; nsameB += c.mode == EFD_FMA && c.same_sign;
        badB += exhaustive32(y, &cmpB); ndB++;
    }
    printf("part B f32 exhaustive: divisors=%d (FMA mode %d, of which same_sign %d), x patterns 2^32 x 5 runs each (P1, P2, P3, P4 permuted, P4 sequential), "
           "elements compared=%lld mismatches=%lld\n", ndB, nfmaB, nsameB, cmpB, badB);

    printf("NaN-bit differences (both NaN, bits differ; informational, not mismatches) f64/f32 per variant:");
    for (int w = 0; w < NVAR; w++) printf(" %s=%lld/%lld", pname[w], nanbits[0][w], nanbits[1][w]);
    printf("\n");
    printf("SUMMARY test_kernels: elements compared=%lld (A f64 %lld, A f32 %lld, B f32-exhaustive %lld) "
           "mismatches=%lld canary_violations=%lld\n", cmp64 + cmp32 + cmpB, cmp64, cmp32, cmpB,
           bad64 + bad32 + badB, total_canary);
    return (bad64 + bad32 + badB + total_canary) != 0;
}
