/* Corollary A4 (compiler fold): for an int32 i, `(double)i / C` equals `fma(x, zh, x*zl)` with x = (double)i,
 * with NO guard, whenever C > 0 is accepted by efd64_setup (then thi >= 2^54 > |i| and tlo <= 1/2), or is
 * rejected only because of a candidate significand with fewer than (53 - 32) trailing zero bits.
 *
 *   mode "test":  for many constants C > 0, compare the two forms bitwise for ALL 2^32 values of an int32
 *                 dividend (and all 2^16 uint16 values for binary32 constants).
 *   mode "bench": time `out[k] = (double)in[k] / C` against the kernel form on int32 input arrays
 *                 (both loops auto-vectorised by the compiler with the same flags).
 * Build: gcc -O3 -mavx2 -mfma -ffp-contract=off -fopenmp int_dividend.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <omp.h>
#include "exact_fdiv.h"

static uint64_t s64 = 0x243F6A8885A308D3ull;
static uint64_t rnd(void) { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; return s64; }
static uint64_t bits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static uint32_t bitsf(float d) { uint32_t b; memcpy(&b, &d, 4); return b; }
static double fromb(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }

/* number of trailing zero bits of a 53-bit significand */
static int tz64(uint64_t v) { return v ? __builtin_ctzll(v) : 64; }

static int run_test(int nrand) {
    static const double fixed[] = { 3, 5, 6, 7, 9, 10, 11, 12, 13, 15, 24, 60, 100, 255, 256, 360, 1000, 1024,
        3600, 86400, 1e6, 1e9, 65535, 32767, 0.1, 0.01, 0.001, 1e-6, 1e-9, 1.8, 2.54, 3.6, 9.80665,
        3.141592653589793, 2.718281828459045, 0.3, 0.7, 1.1, 180.0, 57.29577951308232, 4294967295.0,
        2147483647.0, 1.7320508075688772, 0.30102999566398120, 6.283185307179586, 1e15, 1e-15 };
    int nfixed = sizeof fixed / sizeof fixed[0];
    long long total_bad = 0; int accepted = 0, rej_but_ok = 0, rej_unsafe = 0, n = 0;
    for (int it = 0; it < nfixed + nrand; it++) {
        double C;
        if (it < nfixed) C = fixed[it];
        else {
            uint64_t sig = (rnd() & 0x000FFFFFFFFFFFFFull) | 1;            /* odd significand */
            int e = (int)(rnd() % 60) - 20;                               /* 2^-20 .. 2^39 */
            C = ldexp((double)(sig | (1ull << 52)), e - 52);
        }
        volatile double Cv = C;
        double zh = 1.0 / Cv, rho = fma(-Cv, zh, 1.0), zl = rho / Cv;
        /* Corollary A4: C accepted by the full setup (S1, S2, S3) with thi above every |int32|, or rejected
         * ONLY by the significand check (bad_sig != 0 is set after S1 and S2 passed) with a candidate that no
         * 32-bit integer can have as significand (fewer than 53 - 32 trailing zeros) and x*zl unable to overflow. */
        efd64_t cs; efd64_setup(&cs, C);
        uint64_t bad = cs.bad_sig;
        int accepted_setup = cs.mode == EFD_EXACT || (cs.mode == EFD_FMA && cs.thi > 0x1p31);
        int predicted_ok = accepted_setup || (bad != 0 && tz64(bad) < 53 - 32 && fabs(zl) < 1.0);
        if (accepted_setup) accepted++; else if (predicted_ok) rej_but_ok++; else rej_unsafe++;
        long long nbad = 0;
        #pragma omp parallel for reduction(+:nbad) schedule(static)
        for (long long v = -2147483648LL; v <= 2147483647LL; v++) {
            double x = (double)(int)v;
            double want = x / C, got = fma(x, zh, x * zl);
            if (bits(want) != bits(got)) nbad++;
        }
        n++;
        if (predicted_ok) total_bad += nbad;
        if (nbad || it < nfixed)
            printf("C=%-22.17g bad_sig=%#015llx tz=%2d predicted_ok=%d mismatches over all int32=%lld%s\n",
                   C, (unsigned long long)bad, bad ? tz64(bad) : -1, predicted_ok, nbad,
                   (nbad && predicted_ok) ? "   <-- COUNTEREXAMPLE TO A4" : "");
        fflush(stdout);
    }
    printf("SUMMARY int32 dividends: constants=%d (accepted by setup=%d, rejected by the significand check but safe for 32-bit "
           "integers=%d, rejected and unsafe=%d); mismatches on predicted-ok constants=%lld (each over all 2^32 "
           "int32 values)\n", n, accepted, rej_but_ok, rej_unsafe, total_bad);

    /* binary32 constants with uint16 dividends: all 2^16 values, many constants */
    long long fbad = 0; int fn = 0, facc = 0, frejok = 0;
    for (int it = 0; it < 200000; it++) {
        uint32_t sig = ((uint32_t)rnd() & 0x7FFFFF) | 1;
        int e = (int)(rnd() % 30) - 10;
        float C = ldexpf((float)(sig | (1u << 23)), e - 23);
        if (it == 0) C = 255.0f; if (it == 1) C = 65535.0f; if (it == 2) C = 0.1f; if (it == 3) C = 1000.0f;
        volatile float Cv = C;
        float zh = 1.0f / Cv, rho = fmaf(-Cv, zh, 1.0f), zl = rho / Cv;
        efd32_t cs; efd32_setup(&cs, C);
        uint32_t bad = cs.bad_sig;
        int accepted_setup = cs.mode == EFD_EXACT || (cs.mode == EFD_FMA && cs.thi > 65536.0f);
        int predicted_ok = accepted_setup || (bad != 0 && __builtin_ctz(bad) < 24 - 16 && fabsf(zl) < 1.0f);
        if (!predicted_ok) continue;
        if (accepted_setup) facc++; else frejok++;
        for (uint32_t v = 0; v < 65536; v++) {
            float x = (float)v;
            if (bitsf(x / C) != bitsf(fmaf(x, zh, x * zl))) fbad++;
        }
        fn++;
    }
    printf("SUMMARY uint16 dividends, binary32: constants=%d (accepted by setup=%d, rejected but safe=%d); mismatches=%lld "
           "(each over all 2^16 values)\n", fn, facc, frejok, fbad);
    return (total_bad || fbad) ? 1 : 0;
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

__attribute__((noinline)) static void conv_div(double *restrict out, const int *restrict in, size_t n, double C) {
    for (size_t k = 0; k < n; k++) out[k] = (double)in[k] / C;
}
__attribute__((noinline)) static void conv_fma(double *restrict out, const int *restrict in, size_t n, double zh, double zl) {
    for (size_t k = 0; k < n; k++) { double x = (double)in[k]; out[k] = fma(x, zh, x * zl); }
}
__attribute__((noinline)) static void conv_divf(float *restrict out, const unsigned char *restrict in, size_t n, float C) {
    for (size_t k = 0; k < n; k++) out[k] = (float)in[k] / C;
}
__attribute__((noinline)) static void conv_fmaf(float *restrict out, const unsigned char *restrict in, size_t n, float zh, float zl) {
    for (size_t k = 0; k < n; k++) { float x = (float)in[k]; out[k] = fmaf(x, zh, x * zl); }
}

static int cmpd(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }

static int run_bench(void) {
    static const size_t sizes[] = { 1024, 16384, 262144, 4194304 };
    for (int si = 0; si < 4; si++) {
        size_t n = sizes[si];
        int *in = aligned_alloc(64, n * sizeof(int));
        unsigned char *inb = aligned_alloc(64, n);
        double *o1 = aligned_alloc(64, n * sizeof(double)), *o2 = aligned_alloc(64, n * sizeof(double));
        float *f1 = aligned_alloc(64, n * sizeof(float)), *f2 = aligned_alloc(64, n * sizeof(float));
        for (size_t k = 0; k < n; k++) { in[k] = (int)(rnd() % 2000001) - 1000000; inb[k] = (unsigned char)rnd(); }
        volatile double C = 1000.0; double zh = 1.0 / C, zl = fma(-C, zh, 1.0) / C;
        volatile float Cf = 255.0f; float zhf = 1.0f / Cf, zlf = fmaf(-Cf, zhf, 1.0f) / Cf;
        size_t reps = (size_t)(2e8 / n) + 1; if (reps > 20000) reps = 20000;
        double t[4][15];
        for (int r = 0; r < 15; r++) {
            double a = now(); for (size_t q = 0; q < reps; q++) conv_div(o1, in, n, C); t[0][r] = (now() - a) / (reps * n) * 1e9;
            a = now(); for (size_t q = 0; q < reps; q++) conv_fma(o2, in, n, zh, zl); t[1][r] = (now() - a) / (reps * n) * 1e9;
            a = now(); for (size_t q = 0; q < reps; q++) conv_divf(f1, inb, n, Cf); t[2][r] = (now() - a) / (reps * n) * 1e9;
            a = now(); for (size_t q = 0; q < reps; q++) conv_fmaf(f2, inb, n, zhf, zlf); t[3][r] = (now() - a) / (reps * n) * 1e9;
        }
        if (memcmp(o1, o2, n * sizeof(double)) || memcmp(f1, f2, n * sizeof(float))) { printf("OUTPUT MISMATCH\n"); return 1; }
        for (int v = 0; v < 4; v++) qsort(t[v], 15, sizeof(double), cmpd);
        printf("n=%-8zu int32->double /1000.0: div %.3f ns/elt, mul+fma %.3f ns/elt, speedup %.2fx | "
               "uint8->float /255.0f: div %.3f, mul+fma %.3f, speedup %.2fx   (medians of 15; outputs bit-identical)\n",
               n, t[0][7], t[1][7], t[0][7] / t[1][7], t[2][7], t[3][7], t[2][7] / t[3][7]);
        free(in); free(inb); free(o1); free(o2); free(f1); free(f2);
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc > 1 && argv[1][0] == 'b') return run_bench();
    return run_test(argc > 2 ? atoi(argv[2]) : 100);
}
