/* test_flags.c: compare IEEE exception flags of x / y versus fma(x,zh,x*zl) in the fast range. */
#include <fenv.h>
#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <float.h>
#include "exact_fdiv.h"
#pragma STDC FENV_ACCESS ON

#define HARD (FE_OVERFLOW | FE_UNDERFLOW | FE_INVALID | FE_DIVBYZERO)
static uint64_t rs = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs * 0x2545F4914F6CDD1Dull; }

#define DEFTEST(NAME, T, UT, MBITS, EBITS, FMA, SETUP, SETUPT, DEXP, MAXV, FNAME) \
static const char *NAME##_name = FNAME; \
static UT NAME##_bits(T v) { UT u; memcpy(&u, &v, sizeof u); return u; } \
static T NAME##_from(UT u) { T v; memcpy(&v, &u, sizeof v); return v; } \
static long NAME##_div, NAME##_cases, NAME##_valmis, NAME##_hard, NAME##_inexonly, NAME##_ovf, NAME##_unf, NAME##_fma_div, NAME##_printed; \
static void NAME##_one(T x, T y, SETUPT *c) { \
    volatile T vx = x, vy = y, vzh = c->zh, vzl = c->zl, q1, q2, t; \
    int f1, f2; \
    feclearexcept(FE_ALL_EXCEPT); \
    q1 = vx / vy; \
    f1 = fetestexcept(FE_ALL_EXCEPT); \
    feclearexcept(FE_ALL_EXCEPT); \
    t = vx * vzl; \
    q2 = FMA(vx, vzh, t); \
    f2 = fetestexcept(FE_ALL_EXCEPT); \
    T a = q1, b = q2; \
    NAME##_cases++; \
    if (f1 & FE_OVERFLOW) NAME##_ovf++; \
    if (f1 & FE_UNDERFLOW) NAME##_unf++; \
    int same = (NAME##_bits(a) == NAME##_bits(b)) || (a != a && b != b); \
    if (!same) NAME##_valmis++; \
    if ((f1 ^ f2) & HARD) { \
        NAME##_hard++; \
        if (NAME##_printed < 10) { NAME##_printed++; \
            printf("%s FLAGDIFF x=%a y=%a q1=%a q2=%a f1=0x%x f2=0x%x\n", NAME##_name, (double)x, (double)y, (double)a, (double)b, f1, f2); } \
    } else if ((f1 ^ f2) & FE_INEXACT) NAME##_inexonly++; \
} \
static void NAME##_div_test(T y, int nx) { \
    SETUPT c; SETUP(&c, y); NAME##_div++; \
    if (c.mode != EFD_FMA) return; \
    NAME##_fma_div++; \
    UT lo = NAME##_bits(c.tlo); \
    UT hi = isinf(c.thi) ? (UT)(((UT)((1u << EBITS) - 1)) << MBITS) : NAME##_bits(c.thi); /* exclusive */ \
    if (hi <= lo) return; \
    UT elo = lo >> MBITS, ehi = (hi - 1) >> MBITS; \
    int emask_sign_shift = sizeof(UT) * 8 - 1; \
    for (int i = 0; i < nx; i++) { \
        UT E = elo + (UT)(rnd() % (ehi - elo + 1)); \
        UT m = (UT)rnd() & (((UT)1 << MBITS) - 1); \
        UT u = (E << MBITS) | m; \
        if (u < lo || u >= hi) { i--; if ((rnd() & 63) == 0) i++; continue; } \
        if (rnd() & 1) u |= (UT)1 << emask_sign_shift; \
        NAME##_one(NAME##_from(u), y, &c); \
    } \
    UT s = (UT)1 << emask_sign_shift; \
    NAME##_one(c.tlo, y, &c); NAME##_one(-c.tlo, y, &c); \
    NAME##_one(NAME##_from(lo + 1), y, &c); \
    if (!isinf(c.thi)) { NAME##_one(NAME##_from(hi - 1), y, &c); NAME##_one(NAME##_from((hi - 1) | s), y, &c); } \
    { /* near overflow threshold */ \
        long double ay = y < 0 ? -(long double)y : (long double)y; \
        long double xc = (long double)MAXV * ay; \
        if (xc < (long double)MAXV) { \
            T xt = (T)xc; UT ub = NAME##_bits(xt); \
            for (int d = -6; d <= 6; d++) { \
                UT u = ub + (UT)d; T xv = NAME##_from(u); \
                if (!(xv == xv) || isinf(xv)) continue; \
                T ax = xv < 0 ? -xv : xv; \
                if (ax >= c.tlo && ax < c.thi) { NAME##_one(xv, y, &c); NAME##_one(-xv, y, &c); } \
            } \
        } \
    } \
}

DEFTEST(f64, double, uint64_t, 52, 11, fma, efd64_setup, efd64_t, 0, DBL_MAX, "binary64")
DEFTEST(f32, float, uint32_t, 23, 8, fmaf, efd32_setup, efd32_t, 0, FLT_MAX, "binary32")

#define DRIVER(NAME, T, UT, MBITS, EBITS, BIAS, ND, DIVLIST) \
static void NAME##_run(int nx) { \
    const T *fixed = DIVLIST; \
    for (size_t i = 0; i < sizeof DIVLIST / sizeof DIVLIST[0]; i++) { NAME##_div_test(fixed[i], nx); NAME##_div_test(-fixed[i], nx); } \
    for (int i = 0; i < ND; i++) { /* random bit patterns */ \
        UT u = (UT)rnd(); NAME##_div_test(NAME##_from(u), nx); } \
    for (int i = 0; i < ND; i++) { /* normal, uniform exponent */ \
        UT E = 1 + (UT)(rnd() % (((UT)1 << EBITS) - 2)); \
        UT u = (E << MBITS) | ((UT)rnd() & (((UT)1 << MBITS) - 1)) | ((rnd() & 1) ? ((UT)1 << (EBITS + MBITS)) : 0); \
        NAME##_div_test(NAME##_from(u), nx); } \
    for (int i = 0; i < ND; i++) { /* exponent near 0 */ \
        UT E = (UT)(BIAS + (int)(rnd() % 17) - 8); \
        UT u = (E << MBITS) | ((UT)rnd() & (((UT)1 << MBITS) - 1)) | ((rnd() & 1) ? ((UT)1 << (EBITS + MBITS)) : 0); \
        NAME##_div_test(NAME##_from(u), nx); } \
    printf("SUMMARY %s: divisors=%ld fma_mode=%ld cases=%ld value_mismatches=%ld ovf_unf_inv_dbz_flag_diffs=%ld inexact_only_diffs=%ld overflowed=%ld underflowed=%ld\n", \
        NAME##_name, NAME##_div, NAME##_fma_div, NAME##_cases, NAME##_valmis, NAME##_hard, NAME##_inexonly, NAME##_ovf, NAME##_unf); \
}

static const double f64_fixed[] = {0x1.4p-997, 0x1.8p-1022, 0x1.8p+900, 10.0, 3.0, 255.0, 0.1, 1.0e-300, 1.0e300, 0x1p-1000, 0x1.fffffffffffffp+1023, 0x1p-1022, 0x1.0000000000001p+0, 7.0, 1000.0};
DRIVER(f64, double, uint64_t, 52, 11, 1023, 8000, f64_fixed)
static const float f32_fixed[] = {0x1.4p-97f, 0x1.8p-126f, 0x1.8p+100f, 10.0f, 3.0f, 255.0f, 0.1f, 1.0e-30f, 1.0e30f, 0x1p-100f, 0x1.fffffep+127f, 0x1p-126f, 0x1.000002p+0f, 7.0f, 1000.0f};
DRIVER(f32, float, uint32_t, 23, 8, 127, 8000, f32_fixed)

int main(void) {
    f64_run(600);
    f32_run(600);
    return 0;
}
