/* Throughput benchmark: array / scalar, binary64 and binary32.
 * Variants (all with the same 4-vector unrolling, all noinline, called through a function-pointer table):
 *   div    vdivpd / vdivps loop (div64_array / div32_array)
 *   recip  x * (1/y), INEXACT reference (recip64_array / recip32_array)
 *   raw    unguarded q = fma(x, zh, x*zl), INEXACT outside [tlo, thi) (only to price the guard)
 *   P1 P2 P3 P3X P4  efd kernels with precomputed setup (efdNN_div_array_c; P4 is the default)
 * Data: i normal-range random (|x| = sig * 2^U, U in [-30,30], random sign); ii = i with 10% zeros;
 *       iii = i with 1% NaN; iv = i with 0.1% finite nonzero values below tlo; v = integers 0..255.
 * Timing: rdtscp/lfence around each sample; TSC frequency calibrated against CLOCK_MONOTONIC; ns reported.
 *   out-of-place: one sample = K calls on the same src/dst (K*n >= 65536 elements);
 *   in-place: K copies (K*n*size >= 16 KiB) refreshed by memcpy before the sample (untimed), one call per copy.
 *   variants are sampled interleaved (round robin) within a group; 3 warm-up rounds, then REPS rounds (>= 31
 *   for n <= 65536); median / min / max of ns per element.
 *   A dependent-imul chain measures the core clock (GHz) before each group, to report cycles/element and to
 *   classify the core the vCPU actually ran on (WSL2 does not expose P/E topology).
 * Output: one JSON object per line (JSONL) on stdout; human-readable lines on stderr.
 * Build: gcc -O2 -mavx2 -mfma -ffp-contract=off bench.c -o bench -lm
 * Usage: ./bench full|reduced|setup <cpu_label> [reps=15]
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#ifdef _WIN32
/* Native Windows build (only to pin to a physical E-core, which WSL2 cannot do):
 *   clang -O2 -mavx2 -mfma -ffp-contract=off bench.c -o bench_win.exe
 *   set EFD_AFFINITY=<logical processor index>; the efficiency class of that processor is reported. */
#include <windows.h>
#include <malloc.h>
#define aligned_alloc(a, n) _aligned_malloc((n), (a))
#define CLOCK_MONOTONIC 1
struct efd_ts { long long tv_sec; long tv_nsec; };
#define timespec efd_ts
static int clock_gettime(int id, struct efd_ts *t) {
    (void)id; LARGE_INTEGER f, c; QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c);
    t->tv_sec = c.QuadPart / f.QuadPart; t->tv_nsec = (long)((c.QuadPart % f.QuadPart) * 1000000000LL / f.QuadPart); return 0;
}
static int sched_getcpu(void) { return (int)GetCurrentProcessorNumber(); }
static int efd_win_effclass(int cpu) {             /* EfficiencyClass of logical processor cpu (group 0) */
    DWORD len = 0; GetLogicalProcessorInformationEx(RelationProcessorCore, NULL, &len);
    char *buf = malloc(len); int ec = -1;
    if (GetLogicalProcessorInformationEx(RelationProcessorCore, (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)buf, &len))
        for (DWORD off = 0; off < len;) {
            PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX p = (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)(buf + off);
            if (p->Processor.GroupMask[0].Mask & ((KAFFINITY)1 << cpu)) ec = p->Processor.EfficiencyClass;
            off += p->Size;
        }
    free(buf); return ec;
}
static void efd_win_pin(void) {
    const char *a = getenv("EFD_AFFINITY");
    if (a) {
        int cpu = atoi(a);
        SetThreadAffinityMask(GetCurrentThread(), (DWORD_PTR)1 << cpu);
        SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);
        fprintf(stderr, "pinned to logical processor %d, EfficiencyClass %d\n", cpu, efd_win_effclass(cpu));
    }
}
#else
#include <sched.h>
static void efd_win_pin(void) {}
#endif
#include <x86intrin.h>
#include "efd_kernels.h"

#define NOINLINE __attribute__((noinline))
#define BARRIER() __asm__ volatile("" ::: "memory")

/* ------------------------------------------------ variants ------------------------------------------------ */
typedef struct { efd64_t c; double y; } ctx64;
typedef struct { efd32_t c; float y; } ctx32;

NOINLINE static void v64_div(const ctx64 *k, double *d, const double *s, size_t n) { div64_array(d, s, n, k->y); }
NOINLINE static void v64_recip(const ctx64 *k, double *d, const double *s, size_t n) { recip64_array(d, s, n, k->y); }
NOINLINE static void v64_raw(const ctx64 *k, double *d, const double *s, size_t n) {
    const __m256d zh = _mm256_set1_pd(k->c.zh), zl = _mm256_set1_pd(k->c.zl);
    size_t i = 0;
    for (; i + 16 <= n; i += 16) {
        __m256d q[4];
#pragma GCC unroll 4
        for (int j = 0; j < 4; j++) { __m256d x = _mm256_loadu_pd(s + i + 4 * j); q[j] = _mm256_fmadd_pd(x, zh, _mm256_mul_pd(x, zl)); }
#pragma GCC unroll 4
        for (int j = 0; j < 4; j++) _mm256_storeu_pd(d + i + 4 * j, q[j]);
    }
    for (; i < n; i++) d[i] = fma(s[i], k->c.zh, s[i] * k->c.zl);
}
NOINLINE static void v64_p1(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array_c(&k->c, d, s, n, EFD_P1); }
NOINLINE static void v64_p2(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array_c(&k->c, d, s, n, EFD_P2); }
NOINLINE static void v64_p3(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array_c(&k->c, d, s, n, EFD_P3); }
NOINLINE static void v64_p3x(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array_c(&k->c, d, s, n, EFD_P3X); }
NOINLINE static void v64_p4(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array_c(&k->c, d, s, n, EFD_P4); }
NOINLINE static void v64_entry(const ctx64 *k, double *d, const double *s, size_t n) { efd64_div_array(d, s, n, k->y); }

NOINLINE static void v32_div(const ctx32 *k, float *d, const float *s, size_t n) { div32_array(d, s, n, k->y); }
NOINLINE static void v32_recip(const ctx32 *k, float *d, const float *s, size_t n) { recip32_array(d, s, n, k->y); }
NOINLINE static void v32_raw(const ctx32 *k, float *d, const float *s, size_t n) {
    const __m256 zh = _mm256_set1_ps(k->c.zh), zl = _mm256_set1_ps(k->c.zl);
    size_t i = 0;
    for (; i + 32 <= n; i += 32) {
        __m256 q[4];
#pragma GCC unroll 4
        for (int j = 0; j < 4; j++) { __m256 x = _mm256_loadu_ps(s + i + 8 * j); q[j] = _mm256_fmadd_ps(x, zh, _mm256_mul_ps(x, zl)); }
#pragma GCC unroll 4
        for (int j = 0; j < 4; j++) _mm256_storeu_ps(d + i + 8 * j, q[j]);
    }
    for (; i < n; i++) d[i] = fmaf(s[i], k->c.zh, s[i] * k->c.zl);
}
NOINLINE static void v32_p1(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array_c(&k->c, d, s, n, EFD_P1); }
NOINLINE static void v32_p2(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array_c(&k->c, d, s, n, EFD_P2); }
NOINLINE static void v32_p3(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array_c(&k->c, d, s, n, EFD_P3); }
NOINLINE static void v32_p3x(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array_c(&k->c, d, s, n, EFD_P3X); }
NOINLINE static void v32_p4(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array_c(&k->c, d, s, n, EFD_P4); }
NOINLINE static void v32_entry(const ctx32 *k, float *d, const float *s, size_t n) { efd32_div_array(d, s, n, k->y); }

typedef void (*f64fn)(const ctx64 *, double *, const double *, size_t);
typedef void (*f32fn)(const ctx32 *, float *, const float *, size_t);
#define NV 8
#define V_ENTRY 8
#define V_P4 7
static const char *vname[NV + 1] = { "div", "recip", "raw", "P1", "P2", "P3", "P3X", "P4", "entry" };
static f64fn T64[NV + 1] = { v64_div, v64_recip, v64_raw, v64_p1, v64_p2, v64_p3, v64_p3x, v64_p4, v64_entry };
static f32fn T32[NV + 1] = { v32_div, v32_recip, v32_raw, v32_p1, v32_p2, v32_p3, v32_p3x, v32_p4, v32_entry };

/* ------------------------------------------------ timing ------------------------------------------------ */
static double tsc_ghz;
static inline uint64_t tsc0(void) { _mm_lfence(); uint64_t t = __rdtsc(); _mm_lfence(); return t; }
static inline uint64_t tsc1(void) { unsigned a; uint64_t t = __rdtscp(&a); _mm_lfence(); return t; }
static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void calib_tsc(void) {
    double t0 = now_s(); uint64_t c0 = tsc0();
    while (now_s() - t0 < 0.2) ;
    double t1 = now_s(); uint64_t c1 = tsc1();
    tsc_ghz = (c1 - c0) / (t1 - t0) / 1e9;
}
/* core clock: 2^26 iterations of a 4-deep dependent imul chain (3 cycles each) */
static double core_ghz(void) {
    uint64_t x = 1, n = 1ull << 24;
    uint64_t t0 = tsc0();
    for (uint64_t i = 0; i < n; i++) __asm__ volatile("imul %0, %0\n\timul %0, %0\n\timul %0, %0\n\timul %0, %0" : "+r"(x));
    uint64_t t1 = tsc1();
    return 12.0 * n / ((t1 - t0) / tsc_ghz);   /* imul r64: 3-cycle latency (add-immediate chains are folded at rename on Golden/Redwood Cove) */
}
static double loadavg1(void) { double l = -1; FILE *f = fopen("/proc/loadavg", "r"); if (f) { if (fscanf(f, "%lf", &l) != 1) l = -1; fclose(f); } return l; }
static int cmpd(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }

/* ------------------------------------------------ data ------------------------------------------------ */
static uint64_t rs = 12345;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * 0x1p-53; }
static const char *dname[5] = { "i_normal", "ii_10pct_zero", "iii_1pct_nan", "iv_0.1pct_below_tlo", "v_int_0_255" };

static double gen_d(int data, double tlo) {
    if (data == 4) return (double)(rnd() & 255);
    double u = urand();
    if (data == 1 && u < 0.10) return 0.0;
    if (data == 2 && u < 0.01) return NAN;
    if (data == 3 && u < 0.001) return tlo * ldexp(1.0 + urand(), -2 - (int)(rnd() % 8));   /* finite, nonzero, < tlo */
    double m = 1.0 + urand();
    double v = ldexp(m, (int)(rnd() % 61) - 30);
    return (rnd() & 1) ? -v : v;
}
static float gen_f(int data, float tlo) {
    if (data == 4) return (float)(rnd() & 255);
    double u = urand();
    if (data == 1 && u < 0.10) return 0.0f;
    if (data == 2 && u < 0.01) return NAN;
    if (data == 3 && u < 0.001) return tlo * ldexpf(1.0f + (float)urand(), -2 - (int)(rnd() % 8));
    float m = 1.0f + (float)urand();
    float v = ldexpf(m, (int)(rnd() % 61) - 30);
    return (rnd() & 1) ? -v : v;
}

/* ------------------------------------------------ measurement ------------------------------------------------ */
static const char *cpu_label;
static int reps = 15, cur_cpu = -1;
static double cur_ghz = 0;

typedef struct { double med, mn, mx, med_ticks; int k; } meas_t;

/* one timed sample: ticks per element */
static double sample(int is64, int v, const void *ctx, void *dst, const void *src, void *work, size_t n, int inplace) {
    size_t es = is64 ? 8 : 4;
    int K;
    if (inplace) K = (int)((16384 / (n * es)) ? 16384 / (n * es) : 1);
    else K = (int)((65536 / n) ? 65536 / n : 1);
    uint64_t t0, t1;
    if (inplace) {
        for (int k = 0; k < K; k++) memcpy((char *)work + (size_t)k * n * es, src, n * es);
        BARRIER();
        t0 = tsc0();
        for (int k = 0; k < K; k++) {
            char *p = (char *)work + (size_t)k * n * es;
            if (is64) T64[v](ctx, (double *)p, (const double *)p, n); else T32[v](ctx, (float *)p, (const float *)p, n);
            BARRIER();
        }
        t1 = tsc1();
    } else {
        t0 = tsc0();
        for (int k = 0; k < K; k++) {
            if (is64) T64[v](ctx, dst, src, n); else T32[v](ctx, dst, src, n);
            BARRIER();
        }
        t1 = tsc1();
    }
    return (double)(t1 - t0) / ((double)K * n);
}

/* Interleaved measurement of nv variants: each repetition takes one sample of every variant in turn (rotating
 * the start), so clock/turbo drift during the group affects all variants alike.  3 warm-up rounds. */
static void measure_group(int is64, const int *vars, int nv, const void *ctx, void *dst, const void *src, void *work,
                          size_t n, int inplace, meas_t *out) {
    int R = n <= 65536 ? (reps < 31 ? 31 : reps) : reps;
    double *tk = malloc((size_t)nv * R * sizeof(double));
    for (int r = -3; r < R; r++)
        for (int jj = 0; jj < nv; jj++) {
            int j = (jj + (r < 0 ? 0 : r)) % nv;
            double t = sample(is64, vars[j], ctx, dst, src, work, n, inplace);
            if (r >= 0) tk[(size_t)j * R + r] = t;
        }
    for (int j = 0; j < nv; j++) {
        double *x = tk + (size_t)j * R;
        qsort(x, R, sizeof(double), cmpd);
        out[j].med = x[R / 2] / tsc_ghz; out[j].mn = x[0] / tsc_ghz; out[j].mx = x[R - 1] / tsc_ghz;
        out[j].med_ticks = x[R / 2]; out[j].k = R;
    }
    free(tk);
}

static meas_t measure(int is64, int v, const void *ctx, void *dst, const void *src, void *work, size_t n, int inplace) {
    meas_t m; measure_group(is64, &v, 1, ctx, dst, src, work, n, inplace, &m); return m;
}

static void emit(int is64, const char *var, double y, int mode, int same, int data, size_t n, int inplace, meas_t m) {
    printf("{\"cpu_label\":\"%s\",\"vcpu\":%d,\"core_ghz\":%.3f,\"load1\":%.2f,\"type\":\"%s\",\"variant\":\"%s\","
           "\"divisor\":%.17g,\"mode\":%d,\"same_sign\":%d,\"data\":\"%s\",\"n\":%zu,\"inplace\":%d,"
           "\"median_ns\":%.4f,\"min_ns\":%.4f,\"max_ns\":%.4f,\"median_tsc_ticks\":%.4f,\"est_core_cycles\":%.3f,\"reps\":%d}\n",
           cpu_label, cur_cpu, cur_ghz, loadavg1(), is64 ? "f64" : "f32", var, y, mode, same, data >= 0 ? dname[data] : "none",
           n, inplace, m.med, m.mn, m.mx, m.med_ticks, m.med * cur_ghz, m.k);
    fflush(stdout);
}

static const double DIVS[5] = { 255.0, 3.0, 0.1, 1.7320508075688772, 1e-3 };
static const size_t SIZES[5] = { 256, 4096, 65536, 1 << 20, 1 << 24 };

static void run_group(int is64, int di, int data, int si, void *src, void *dst, void *work) {
    size_t n = SIZES[si];
    double y = DIVS[di];
    ctx64 k64; ctx32 k32;
    k64.y = y; efd64_setup(&k64.c, y); k32.y = (float)y; efd32_setup(&k32.c, (float)y);
    rs = 0x1234567ull + 7919 * di + 104729 * data;
    if (is64) { double *s = src; for (size_t i = 0; i < n; i++) s[i] = gen_d(data, k64.c.tlo); }
    else { float *s = src; for (size_t i = 0; i < n; i++) s[i] = gen_f(data, k32.c.tlo); }
    cur_cpu = sched_getcpu(); cur_ghz = core_ghz();
    int mode = is64 ? k64.c.mode : k32.c.mode, same = is64 ? k64.c.same_sign : k32.c.same_sign;
    for (int ip = 0; ip < 2; ip++) {
        int vars[NV], nv = 0;
        for (int v = 0; v < NV; v++) if (!(v == 2 && mode != EFD_FMA)) vars[nv++] = v;
        meas_t ms[NV];
        double g0 = core_ghz();
        measure_group(is64, vars, nv, is64 ? (void *)&k64 : (void *)&k32, dst, src, work, n, ip, ms);
        double g1 = core_ghz();
        cur_ghz = 0.5 * (g0 + g1);
        for (int vi = 0; vi < nv; vi++) {
            int v = vars[vi]; meas_t m = ms[vi];
            emit(is64, vname[v], y, mode, same, data, n, ip, m);
            fprintf(stderr, "%s y=%-8g %-20s n=%-9zu %s %-5s med=%.4f ns (min %.4f max %.4f) ghz=%.2f cpu=%d load=%.2f\n",
                    is64 ? "f64" : "f32", y, dname[data], n, ip ? "inpl" : "outp", vname[v], m.med, m.mn, m.mx, cur_ghz,
                    cur_cpu, loadavg1());
        }
        }
}

/* setup cost and break-even */
static volatile double sinkd; static volatile float sinkf;
static void run_setup(void) {
    static double ys[4096]; static float yf[4096];
    rs = 99;
    for (int i = 0; i < 4096; i++) { ys[i] = ldexp(1.0 + urand(), (int)(rnd() % 41) - 20); yf[i] = (float)ys[i]; }
    for (int pass = 0; pass < 2; pass++) {
        /* (a) random moderate divisors, (b) each benchmark divisor repeatedly */
        for (int which = -1; which < 5; which++) {
            double best64 = 1e30, best32 = 1e30, s64v[15], s32v[15];
            volatile double yv = which < 0 ? 0 : DIVS[which]; volatile float yvf = (float)yv;
            char dstr[40]; if (which < 0) snprintf(dstr, sizeof dstr, "\"random_4096\""); else snprintf(dstr, sizeof dstr, "%.17g", DIVS[which]);
            for (int r = 0; r < 15; r++) {
                uint64_t t0 = tsc0();
                for (int i = 0; i < 4096; i++) { efd64_t c; efd64_setup(&c, which < 0 ? ys[i] : yv); sinkd = c.zl; }
                uint64_t t1 = tsc1();
                for (int i = 0; i < 4096; i++) { efd32_t c; efd32_setup(&c, which < 0 ? yf[i] : yvf); sinkf = c.zl; }
                uint64_t t2 = tsc1();
                s64v[r] = (t1 - t0) / tsc_ghz / 4096; s32v[r] = (t2 - t1) / tsc_ghz / 4096;
                if (s64v[r] < best64) best64 = s64v[r];
                if (s32v[r] < best32) best32 = s32v[r];
            }
            qsort(s64v, 15, sizeof(double), cmpd); qsort(s32v, 15, sizeof(double), cmpd);
            if (pass == 1)
                printf("{\"cpu_label\":\"%s\",\"vcpu\":%d,\"load1\":%.2f,\"kind\":\"setup\",\"divisor\":%s,"
                       "\"f64_setup_ns_median\":%.2f,\"f64_setup_ns_min\":%.2f,\"f32_setup_ns_median\":%.2f,\"f32_setup_ns_min\":%.2f}\n",
                       cpu_label, sched_getcpu(), loadavg1(), dstr,
                       s64v[7], best64, s32v[7], best32);
        }
    }
    /* break-even: entry point (setup + P3) vs div, out of place, small n, in cache */
    static double s[1024], d[1024]; static float sf[1024], df[1024];
    for (int i = 0; i < 1024; i++) { s[i] = gen_d(0, 1e-300); sf[i] = gen_f(0, 1e-30f); }
    static const size_t ns[] = { 1, 2, 4, 8, 16, 24, 32, 48, 64, 96, 128, 192, 256, 512, 1024 };
    cur_cpu = sched_getcpu(); cur_ghz = core_ghz();
    for (int di = 0; di < 5; di++) {
        ctx64 k64; ctx32 k32; k64.y = DIVS[di]; efd64_setup(&k64.c, DIVS[di]); k32.y = (float)DIVS[di]; efd32_setup(&k32.c, (float)DIVS[di]);
        for (size_t q = 0; q < sizeof ns / sizeof ns[0]; q++) {
            for (int is64 = 1; is64 >= 0; is64--) {
                int vv[3] = { 0, V_ENTRY, V_P4 };   /* div, entry (setup + default P4), P4 */
                for (int t = 0; t < 3; t++) {
                    meas_t m = measure(is64, vv[t], is64 ? (void *)&k64 : (void *)&k32, is64 ? (void *)d : (void *)df,
                                       is64 ? (void *)s : (void *)sf, NULL, ns[q], 0);
                    printf("{\"cpu_label\":\"%s\",\"vcpu\":%d,\"core_ghz\":%.3f,\"load1\":%.2f,\"kind\":\"breakeven\",\"type\":\"%s\","
                           "\"variant\":\"%s\",\"divisor\":%.17g,\"n\":%zu,\"median_ns_per_call\":%.3f,\"min_ns_per_call\":%.3f}\n",
                           cpu_label, cur_cpu, cur_ghz, loadavg1(), is64 ? "f64" : "f32", vname[vv[t]], DIVS[di], ns[q],
                           m.med * ns[q], m.mn * ns[q]);
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s full|reduced|setup cpu_label [reps]\n", argv[0]); return 2; }
    cpu_label = argv[2]; if (argc > 3) reps = atoi(argv[3]);
    efd_win_pin();
    calib_tsc();
    fprintf(stderr, "tsc %.4f GHz, core clock now %.3f GHz, vcpu %d, load %.2f\n", tsc_ghz, core_ghz(), sched_getcpu(), loadavg1());
    printf("{\"kind\":\"meta\",\"cpu_label\":\"%s\",\"tsc_ghz\":%.4f,\"vcpu\":%d,\"load1_start\":%.2f}\n", cpu_label, tsc_ghz, sched_getcpu(), loadavg1());
    for (int di = 0; di < 5; di++) {
        efd64_t c; efd64_setup(&c, DIVS[di]); efd32_t f; efd32_setup(&f, (float)DIVS[di]);
        printf("{\"kind\":\"divisor\",\"divisor\":%.17g,\"f64_mode\":%d,\"f64_same_sign\":%d,\"f64_tlo\":\"%a\",\"f64_thi\":\"%a\","
               "\"f32_mode\":%d,\"f32_same_sign\":%d,\"f32_tlo\":\"%a\",\"f32_thi\":\"%a\"}\n", DIVS[di], c.mode, c.same_sign, c.tlo, c.thi,
               f.mode, f.same_sign, (double)f.tlo, (double)f.thi);
    }
    if (argv[1][0] == 'p') return 0;                     /* probe: pin, report, exit */
    if (argv[1][0] == 's') { run_setup(); return 0; }
    int full = argv[1][0] == 'f';
    size_t maxn = SIZES[4];
    void *src = aligned_alloc(64, maxn * 8), *dst = aligned_alloc(64, maxn * 8), *work = aligned_alloc(64, maxn * 8 + 65536);
    memset(dst, 0, maxn * 8); memset(work, 0, maxn * 8);
    for (int is64 = 1; is64 >= 0; is64--)
        for (int si = 0; si < 5; si++)
            for (int di = 0; di < 5; di++)
                for (int data = 0; data < 5; data++) {
                    int big = si >= 3;
                    if (full) { if (big && !(data == 0 || di == 0)) continue; }
                    else { if (!((di == 1 && data == 0) || (di == 0 && (data == 0 || data == 4)))) continue; }
                    run_group(is64, di, data, si, src, dst, work);
                }
    printf("{\"kind\":\"meta_end\",\"load1_end\":%.2f}\n", loadavg1());
    return 0;
}
