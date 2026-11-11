/* Adversarial scalar test of efd64_div (exact_fdiv.h) against hardware x / y in binary64.
 * Divisors: structured list (+ negatives), NR random bit patterns, NR random significands with exponents near 0.
 * Families of x per divisor:
 *   a  uniformly random bit patterns
 *   b  x at / just below / just above tlo and thi (+-4 ulps) and scaled copies (random significand, same
 *      binade edge: T*(1 -+ j*2^-53), T*2^-1, T*2^1)
 *   c  near-midpoint: random odd 54-bit M, x = RN(M * Y * 2^s) (exact 107-bit product rounded to 53 bits) at a
 *      random binade (uniform over all binades, plus extra weight near tlo/thi and the quotient-overflow and
 *      quotient-underflow binades), and its neighbours +-1, +-2 ulps
 *   d  for odd Y: the two Theorem-A candidate significands X with X*2^54 = B*Y -+ 1 (B = P-, P+ as in
 *      efd64_bad_significand) and neighbours X-2..X+2, at every binade exponent (structured divisors and every
 *      16th random divisor) or at 160 sampled exponents (incl. the edges: tlo, thi, quotient overflow, quotient
 *      smallest normal), both signs
 *   e  x with x/y near the overflow threshold (x near DBL_MAX*|y|) and near the smallest normal (x near
 *      DBL_MIN*|y|) and in the subnormal-quotient range, +-8 ulps and random significands in those binades
 *   f  special values (+-0, +-inf, quiet/signalling NaNs with payloads, extremes, subnormal edges, 1, ...)
 * For every divisor rejected because bad_sig != 0: check that the raw kernel fma(x, zh, x*zl) really is wrong on
 * x = bad_sig scaled into the binade of |y| (quotient in (1/2, 1), nothing underflows).
 * Build: gcc -O2 -mavx2 -mfma -ffp-contract=off -fopenmp test_f64.c -o test_f64 -lm
 * Usage: ./test_f64 [NR=20000] [seed=1]
 */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include "exact_fdiv.h"

typedef struct { uint64_t s; } rng_t;
static uint64_t rnd(rng_t *r) {                       /* splitmix64 */
    uint64_t z = (r->s += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31);
}
static double d_of(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static uint64_t b_of(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }

enum { FA, FB, FC, FD, FE, FF, NFAM };
static const char *famname[NFAM] = { "a_random_bits", "b_thresholds", "c_near_midpoint", "d_candidates",
                                     "e_quotient_edges", "f_specials" };

typedef struct { long long cmp[NFAM], bad[NFAM]; } acc_t;
static int printed = 0;

static inline void check(const efd64_t *c, double x, int fam, acc_t *A) {
    double want = x / c->y, got = efd64_div(c, x);
    A->cmp[fam]++;
    if (b_of(want) != b_of(got) && !(want != want && got != got)) {
        A->bad[fam]++;
        int k;
        #pragma omp atomic capture
        k = printed++;
        if (k < 30)
            printf("MISMATCH fam=%s x=0x%016llx (%a) y=0x%016llx (%a) got=%a want=%a mode=%d same=%d tlo=%a thi=%a\n",
                   famname[fam], (unsigned long long)b_of(x), x, (unsigned long long)b_of(c->y), c->y, got, want,
                   c->mode, c->same_sign, c->tlo, c->thi);
    }
}
static inline void check_pm(const efd64_t *c, double x, int fam, acc_t *A) { check(c, x, fam, A); check(c, -x, fam, A); }

/* x = significand S (53-bit integer, 2^52 <= S < 2^53) times 2^(E-52), E = unbiased exponent of the result */
static double mk(uint64_t S, int E) { return ldexp((double)S, E - 52); }

static int ilogb_abs(double v) { return ilogb(fabs(v)); }

static void test_divisor(double y, uint64_t seed, int full_exp, acc_t *A) {
    rng_t R = { seed };
    efd64_t c; efd64_setup(&c, y);
    /* (f) specials */
    static const uint64_t sp[] = { 0, 0x7FF0000000000000ull, 0x7FF8000000000000ull, 0x7FF0000000000001ull,
        0x7FF4000000000000ull, 0x7FFFFFFFFFFFFFFFull, 0x7FF8000000000001ull, 0x0000000000000001ull,
        0x000FFFFFFFFFFFFFull, 0x0010000000000000ull, 0x0010000000000001ull, 0x7FEFFFFFFFFFFFFFull,
        0x7FE0000000000000ull, 0x3FF0000000000000ull, 0x3FEFFFFFFFFFFFFFull, 0x0008000000000000ull,
        0x0000000000000002ull, 0x001FFFFFFFFFFFFFull, 0x0020000000000000ull, 0x3CA0000000000000ull,
        0x4340000000000000ull, 0x7FDFFFFFFFFFFFFFull };
    for (size_t i = 0; i < sizeof sp / sizeof sp[0]; i++) check_pm(&c, d_of(sp[i]), FF, A);
    check_pm(&c, y, FF, A); check_pm(&c, nextafter(y, 0), FF, A); check_pm(&c, nextafter(y, 2 * y), FF, A);

    /* (a) random bit patterns */
    for (int i = 0; i < 32768; i++) check(&c, d_of(rnd(&R)), FA, A);

    int ey = ilogb_abs(y);                                  /* |y| in [2^ey, 2^(ey+1)) for normal y */
    int Eovf = 1023 + ey, Emin = -1022 + ey;                /* binades of x where x/y ~ 2^1023 resp. ~ 2^-1022 */
    int Etlo = c.tlo > 0 ? ilogb(c.tlo) : -1022, Ethi = (c.thi > 0 && isfinite(c.thi)) ? ilogb(c.thi) : 1023;

    /* (b) thresholds */
    double Ts[2] = { c.tlo > 0 ? c.tlo : DBL_MIN, (c.thi > 0 && isfinite(c.thi)) ? c.thi : DBL_MAX };
    for (int t = 0; t < 2; t++) {
        double T = Ts[t];
        double v = T; for (int k = 0; k < 5; k++) v = nextafter(v, 0);
        for (int k = 0; k < 10; k++) { check_pm(&c, v, FB, A); v = nextafter(v, INFINITY); }
        static const double sc[] = { 0.5, 2.0, 0.25, 4.0 };
        for (int s = 0; s < 4; s++) { double u = T * sc[s]; check_pm(&c, u, FB, A); check_pm(&c, nextafter(u, 0), FB, A);
                                      check_pm(&c, nextafter(u, INFINITY), FB, A); }
        for (int k = 0; k < 16; k++) {                     /* random significands in the binades on both sides */
            uint64_t S = (1ull << 52) | (rnd(&R) & ((1ull << 52) - 1));
            int E = ilogb(T);
            check_pm(&c, mk(S, E), FB, A); check_pm(&c, mk(S, E - 1), FB, A);
        }
    }
    if (c.mode != EFD_FMA && c.mode != EFD_EXACT && !isnormal(y)) return;   /* families c-e need a normal y */
    if (!isnormal(y)) return;
    uint64_t Y = (uint64_t)ldexp(frexp(fabs(y), &(int){0}), 53);

    /* (c) near-midpoint */
    for (int i = 0; i < 4096; i++) {
        uint64_t M = (1ull << 53) | (rnd(&R) & ((1ull << 53) - 1)) | 1;     /* odd, 54 bits */
        unsigned __int128 P = (unsigned __int128)M * Y;                      /* 106 or 107 bits */
        int L = 128 - (int)((P >> 64) ? __builtin_clzll((uint64_t)(P >> 64)) : 64 + __builtin_clzll((uint64_t)P));
        int s = L - 53;
        unsigned __int128 Rr = P >> s, rem = P & (((unsigned __int128)1 << s) - 1), half = (unsigned __int128)1 << (s - 1);
        if (rem > half || (rem == half && (Rr & 1))) Rr++;
        if (Rr >> 53) { Rr >>= 1; }
        uint64_t S = (uint64_t)Rr;
        int E;
        switch (rnd(&R) % 6) {
        case 0: case 1: E = -1074 + (int)(rnd(&R) % 2098); break;            /* anywhere (subnormal x too) */
        case 2: E = Etlo - 3 + (int)(rnd(&R) % 7); break;
        case 3: E = Ethi - 3 + (int)(rnd(&R) % 7); break;
        case 4: E = Eovf - 3 + (int)(rnd(&R) % 7); break;
        default: E = Emin - 3 + (int)(rnd(&R) % 7); break;
        }
        if (E > 1023) E = 1023;
        double x = mk(S, E);
        if (rnd(&R) & 1) x = -x;
        double u = nextafter(nextafter(x, -INFINITY), -INFINITY);
        for (int k = 0; k < 5; k++) { check(&c, u, FC, A); u = nextafter(u, INFINITY); }
    }

    /* (d) Theorem-A candidates */
    if (Y & 1) {
        const uint64_t mask = (1ull << 54) - 1;
        uint64_t Pm = efd_inv64(Y) & mask;
        for (int k = 0; k < 2; k++) {
            uint64_t B = k ? (mask + 1 - Pm) : Pm;
            unsigned __int128 t = (unsigned __int128)B * Y;
            uint64_t X = (uint64_t)((k ? t + 1 : t - 1) >> 54);
            if (X < (1ull << 52) + 2 || X >= (1ull << 53) - 2) continue;
            int ne = full_exp ? 2046 : 160;
            for (int ei = 0; ei < ne; ei++) {
                int E;
                if (full_exp) E = -1022 + ei;
                else switch (ei % 8) {
                    case 0: E = Etlo - 2 + (int)(rnd(&R) % 5); break;
                    case 1: E = Ethi - 2 + (int)(rnd(&R) % 5); break;
                    case 2: E = Eovf - 2 + (int)(rnd(&R) % 5); break;
                    case 3: E = Emin - 2 + (int)(rnd(&R) % 5); break;
                    default: E = -1022 + (int)(rnd(&R) % 2046);
                }
                if (E > 1023 || E < -1074) continue;
                for (int d = -2; d <= 2; d++) check_pm(&c, mk(X + d, E), FD, A);
            }
        }
    }

    /* (e) quotient edges */
    double bases[3] = { DBL_MAX * fabs(y), DBL_MIN * fabs(y), 0x1p-1060 * fabs(y) };
    for (int b = 0; b < 3; b++) {
        double x0 = bases[b];
        if (!(x0 > 0) || isinf(x0)) {          /* threshold outside the x range: use the extreme x instead */
            x0 = b == 0 ? DBL_MAX : 0x1p-1074;
        }
        double v = x0; for (int k = 0; k < 8; k++) v = nextafter(v, 0);
        for (int k = 0; k < 17; k++) { check_pm(&c, v, FE, A); v = nextafter(v, INFINITY); }
        int E = ilogb(x0);
        for (int k = 0; k < 64; k++) {
            uint64_t S = (1ull << 52) | (rnd(&R) & ((1ull << 52) - 1));
            check_pm(&c, mk(S, E), FE, A); if (E < 1023) check_pm(&c, mk(S, E + 1), FE, A); check_pm(&c, mk(S, E - 1), FE, A);
        }
    }
}

int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 20000;
    uint64_t seed = argc > 2 ? strtoull(argv[2], 0, 0) : 1;
    static const double fixed[] = { 3, 10, 255, 1000, 0.1, 1e-3, 3.141592653589793, 2.718281828459045,
        1.7320508075688772, 7, 9, 11, 49, 360, 1e6, 1e9, 1e15, 9007199254740991.0, 4503599627370497.0, 0.3,
        1, 2, 0.5, 4, 1024, 0x1p-1022, 0x1p-1021, 0x1p1023, 0x1p-1000, 0x1p1000, 0x1p-1020, 0x1p1022,
        DBL_MIN, 3 * DBL_MIN, 1.5 * 0x1p-1022, 1e-307, 1e-300, 1e-200, 1e-100, 1e100, 1e200, 1e300, 1e307, 1e308,
        DBL_MAX, 0x1.fffffffffffffp1022, 0x1.0000000000001p1023, 3 * 0x1p1021, 0x1.5555555555555p-1022,
        0x1.0000000000001p0, 0x1.fffffffffffffp0, 0x1.fffffffffffffp-1, 0x1.0000000000001p-1022, 0x1.8p-1021,
        1e-310, 0x1p-1074, 0.0, INFINITY, NAN, 6.02214076e23, 1.602176634e-19, 9.80665, 0.7071067811865476 };
    int nf = sizeof fixed / sizeof fixed[0];
    int ND = 2 * nf + 2 * NR;
    double *ys = malloc(ND * sizeof(double)); int *cat = malloc(ND * sizeof(int));
    rng_t R = { seed * 0xD1B54A32D192ED03ull };
    for (int i = 0; i < ND; i++) {
        if (i < 2 * nf) { ys[i] = (i & 1) ? -fixed[i / 2] : fixed[i / 2]; cat[i] = 0; }
        else if (i < 2 * nf + NR) { ys[i] = d_of(rnd(&R)); cat[i] = 1; }
        else { ys[i] = d_of((rnd(&R) & 0x800FFFFFFFFFFFFFull) | ((uint64_t)(1023 - 40 + rnd(&R) % 81) << 52)); cat[i] = 2; }
    }
    /* mode statistics per category: [cat][0..2] modes, [3] same_sign among FMA, [4] rejected by significand,
       [5] odd significand (normal y), [6] count */
    long long st[3][7] = { { 0 } };
    long long rej_total = 0, rej_confirmed = 0;
    acc_t T = { { 0 }, { 0 } };
    double t0 = omp_get_wtime();
    #pragma omp parallel
    {
        acc_t A = { { 0 }, { 0 } };
        long long lst[3][7] = { { 0 } }, lrt = 0, lrc = 0;
        #pragma omp for schedule(dynamic, 16)
        for (int i = 0; i < ND; i++) {
            double y = ys[i];
            efd64_t c; efd64_setup(&c, y);
            int k = cat[i];
            lst[k][c.mode]++; lst[k][6]++;
            if (c.mode == EFD_FMA) lst[k][3] += c.same_sign;
            if (c.bad_sig) lst[k][4]++;
            if (isnormal(y)) { int e; uint64_t Y = (uint64_t)ldexp(frexp(fabs(y), &e), 53); lst[k][5] += Y & 1; }
            if (c.bad_sig) {                              /* rejection necessary? */
                double zh = 1.0 / y, rho = fma(-y, zh, 1.0), zl = rho / y;
                double x = ldexp((double)c.bad_sig, ilogb(fabs(y)) - 52);
                lrt++;
                double raw = fma(x, zh, x * zl), want = x / y;
                if (b_of(raw) != b_of(want)) lrc++;
                else {
                    #pragma omp critical
                    printf("REJECTION NOT CONFIRMED y=%a bad_sig=0x%014llx x=%a raw=%a want=%a\n", y,
                           (unsigned long long)c.bad_sig, x, raw, want);
                }
            }
            int full = (k == 0) || (i % 16 == 0);
            test_divisor(y, seed * 1000003ull + (uint64_t)i * 0x9E3779B97F4A7C15ull, full, &A);
        }
        #pragma omp critical
        {
            for (int f = 0; f < NFAM; f++) { T.cmp[f] += A.cmp[f]; T.bad[f] += A.bad[f]; }
            for (int a = 0; a < 3; a++) for (int b = 0; b < 7; b++) st[a][b] += lst[a][b];
            rej_total += lrt; rej_confirmed += lrc;
        }
    }
    double t1 = omp_get_wtime();
    long long tc = 0, tb = 0;
    printf("per-family comparisons / mismatches:\n");
    for (int f = 0; f < NFAM; f++) { printf("  %-18s %14lld  %lld\n", famname[f], T.cmp[f], T.bad[f]); tc += T.cmp[f]; tb += T.bad[f]; }
    static const char *cn[3] = { "structured(+-)", "random-bits", "random-sig-exp-near-0" };
    printf("mode histogram per divisor category:\n");
    for (int k = 0; k < 3; k++) {
        long long n = st[k][6];
        printf("  %-22s n=%-6lld DIV=%lld (%.3f%%) EXACT=%lld (%.3f%%) FMA=%lld (%.3f%%) | same_sign among FMA=%lld (%.3f%%) "
               "| rejected by significand=%lld (%.3f%% of all, %.3f%% of odd-significand normal y; odd=%lld)\n",
               cn[k], n, st[k][0], 100.0 * st[k][0] / n, st[k][1], 100.0 * st[k][1] / n, st[k][2], 100.0 * st[k][2] / n,
               st[k][3], st[k][2] ? 100.0 * st[k][3] / st[k][2] : 0.0, st[k][4], 100.0 * st[k][4] / n,
               st[k][5] ? 100.0 * st[k][4] / st[k][5] : 0.0, st[k][5]);
    }
    printf("rejected-by-significand divisors: %lld, raw kernel confirmed wrong on x=bad_sig: %lld\n", rej_total, rej_confirmed);
    printf("SUMMARY test_f64: divisors=%d comparisons=%lld mismatches=%lld rejections_confirmed=%lld/%lld time=%.1fs\n",
           ND, tc, tb, rej_confirmed, rej_total, t1 - t0);
    return tb != 0 || rej_confirmed != rej_total;
}
