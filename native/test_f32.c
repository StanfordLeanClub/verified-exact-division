/* Exhaustive binary32 validation of exact_fdiv.h against hardware division.
 *   mode "x":  for each divisor in a list (structured + random bit patterns) compare efd32_div(x) with x / y for
 *              ALL 2^32 bit patterns of x.  NaN results are compared as "both NaN".
 *   mode "sig": for random significands Y, compare the checker's verdict with an exhaustive scan of all 2^23
 *              significands X (unguarded kernel, x and y in [1,2)): bad_sig == 0 <=> no failing X, and when
 *              bad_sig != 0 it is the unique failing X.
 * Build: gcc -O2 -mfma -mavx2 -ffp-contract=off -fopenmp test_f32.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include "exact_fdiv.h"

static uint64_t s64 = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; return s64; }
static float fromb(uint32_t b) { float f; memcpy(&f, &b, 4); return f; }
static uint32_t tob(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }

static int run_x(int nrand, uint64_t seed) {
    static const float fixed[] = { 3, 5, 6, 7, 9, 10, 11, 12, 14, 15, 60, 100, 255, 1000, 1e6f, 1e9f, 0.1f, 0.3f,
        1e-3f, 3.14159274f, 2.71828175f, 1.5f, 2.5f, 0.75f, 1e-30f, 1e30f, 3e38f, 1.2e-38f, 2e-38f, 1e-36f,
        16777215.0f, 8388609.0f, 1.00000012f, 1.99999988f, 0.99999994f, 2.0f, 0.5f, 1.0f, 1024.0f, 4.7e-38f,
        1e-45f, 0.0f, 1e-40f, 2.3e38f, 49.0f, 1.8f, 9.80665f, 360.0f, 6.28318548f, 255.5f };
    int nfixed = sizeof fixed / sizeof fixed[0];
    int total = 2 * nfixed + nrand;
    s64 = seed;
    long long grand_bad = 0; int modes[3] = {0, 0, 0}; int same = 0;
    double fast_frac_sum = 0; int nfma = 0;
    for (int i = 0; i < total; i++) {
        float y;
        if (i < 2 * nfixed) y = (i & 1) ? -fixed[i / 2] : fixed[i / 2];
        else {
            uint32_t b = (uint32_t)rnd();
            if (i % 5 == 0) b = (b & 0x807FFFFFu) | ((uint32_t)(100 + rnd() % 56) << 23);   /* moderate exponents */
            y = fromb(b);
        }
        efd32_t c; efd32_setup(&c, y);
        modes[c.mode]++; if (c.mode == EFD_FMA) same += c.same_sign;
        long long bad = 0, fast = 0;
        #pragma omp parallel for reduction(+:bad,fast) schedule(static)
        for (long long xb = 0; xb < (1LL << 32); xb++) {
            float x = fromb((uint32_t)xb);
            float want = x / y, got = efd32_div(&c, x);
            if (tob(want) != tob(got) && !(want != want && got != got)) bad++;
            if (c.mode == EFD_FMA) { float a = fabsf(x); if (a >= c.tlo && a < c.thi) fast++; }
        }
        if (c.mode == EFD_FMA) { fast_frac_sum += (double)fast / 4294967296.0; nfma++; }
        grand_bad += bad;
        if (bad || i < 2 * nfixed)
            printf("y=%-14.9g (0x%08x) mode=%d same=%d tlo=%-12.6g thi=%-12.6g bad_sig=0x%06x fast=%.4f mismatches=%lld\n",
                   y, tob(y), c.mode, c.same_sign, c.tlo, c.thi, c.bad_sig, (double)fast / 4294967296.0, bad);
        fflush(stdout);
    }
    printf("SUMMARY x-exhaustive: divisors=%d (DIV=%d EXACT=%d FMA=%d, of FMA same-sign=%d) "
           "mean fast-path fraction over all 2^32 bit patterns=%.4f total mismatches=%lld\n",
           total, modes[0], modes[1], modes[2], same, nfma ? fast_frac_sum / nfma : 0.0, grand_bad);
    return grand_bad != 0;
}

static int run_sig(int n, uint64_t seed) {
    s64 = seed;
    long long disagree = 0, nbad = 0, neven = 0;
    for (int i = 0; i < n; i++) {
        uint32_t Y = (1u << 23) | (uint32_t)(rnd() & 0x7FFFFF);
        if (i % 16) Y |= 1; else neven++;
        float y = (float)Y / 8388608.0f;
        float zh = 1.0f / y, rho = fmaf(-y, zh, 1.0f), zl = rho / y;
        long long fails = 0; uint32_t firstX = 0;
        #pragma omp parallel for reduction(+:fails) schedule(static)
        for (uint32_t X = 1u << 23; X < (1u << 24); X++) {
            float x = (float)X / 8388608.0f;
            if (fmaf(x, zh, x * zl) != x / y) { fails++;
                #pragma omp critical
                firstX = X; }
        }
        uint32_t b = efd32_bad_significand(Y);
        nbad += (b != 0);
        if ((b == 0) != (fails == 0) || (b != 0 && (fails != 1 || firstX != b))) {
            disagree++;
            printf("DISAGREE Y=0x%06x checker bad_sig=0x%06x exhaustive fails=%lld X=0x%06x\n", Y, b, fails, firstX);
        }
    }
    printf("SUMMARY significand check: %d significands (%lld even), %lld rejected (%.3f%%), disagreements with "
           "exhaustive scan=%lld\n", n, neven, nbad, 100.0 * nbad / n, disagree);
    return disagree != 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s x|sig count seed\n", argv[0]); return 2; }
    int n = atoi(argv[2]); uint64_t seed = strtoull(argv[3], 0, 0);
    return argv[1][0] == 'x' ? run_x(n, seed) : run_sig(n, seed);
}
