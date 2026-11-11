/* Core-clock probe per vCPU (WSL2 exposes no P/E topology): pins itself to each vCPU in turn and times a
 * dependent imul chain (3 cycles per imul) plus a vdivpd-throughput loop.  Prints GHz and vdivpd ymm cycles.
 * Build: gcc -O2 -mavx2 cpuprobe.c -o cpuprobe      Usage: ./cpuprobe [rounds=3] */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <sched.h>
#include <time.h>
#include <unistd.h>
#include <immintrin.h>
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static double ghz(void) {
    unsigned long long x = 1, n = 1ull << 25; double t0 = now();
    for (unsigned long long i = 0; i < n; i++) __asm__ volatile("imul %0, %0\n\timul %0, %0\n\timul %0, %0\n\timul %0, %0" : "+r"(x));
    return 12.0 * n / (now() - t0) / 1e9;   /* 4 dependent imul, 3 cycles each */
}
static double divns(void) {                          /* 8 independent vdivpd chains: throughput-bound */
    __m256d a[8], y = _mm256_set1_pd(1.0000001);
    for (int j = 0; j < 8; j++) a[j] = _mm256_set1_pd(1.0 + j);
    long n = 1 << 21; double t0 = now();
    for (long i = 0; i < n; i++)
        for (int j = 0; j < 8; j++) { a[j] = _mm256_div_pd(a[j], y); __asm__ volatile("" : "+x"(a[j])); }
    double t = now() - t0; volatile double s = a[0][0]; (void)s;
    return t / (8.0 * n) * 1e9;
}
int main(int argc, char **argv) {
    int rounds = argc > 1 ? atoi(argv[1]) : 3, ncpu = sysconf(_SC_NPROCESSORS_ONLN);
    for (int r = 0; r < rounds; r++)
        for (int c = 0; c < ncpu; c++) {
            cpu_set_t s; CPU_ZERO(&s); CPU_SET(c, &s); sched_setaffinity(0, sizeof s, &s);
            double g = ghz(), d = divns();
            printf("round %d vcpu %2d  imul-chain %.2f GHz  vdivpd-ymm %.2f ns (= %.1f cycles at that clock)\n", r, c, g, d, d * g);
            fflush(stdout);
        }
    return 0;
}
