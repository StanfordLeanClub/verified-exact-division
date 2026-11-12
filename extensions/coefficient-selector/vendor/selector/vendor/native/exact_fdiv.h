/* exact_fdiv.h — division by an invariant IEEE-754 divisor without a divide, bit-identical to x / y.
 *
 *   setup(y)        once per divisor (two divisions, one fma, one modular inverse, <= 2 test evaluations)
 *   q = fma(x, zh, x*zl)   per element, for tlo <= |x| < thi
 *
 * Mathematics: Brisebarre, Muller, Raina, IEEE TC 53(8) 2004 (Algorithm 2), extended here to full IEEE semantics
 * (THEOREM.md, Theorems A and B).  Requires round-to-nearest-even and a correctly rounded fma.
 * Compile with -ffp-contract=off (the code must not be re-contracted or re-associated).
 *
 * mode:
 *   EFD_DIV    unsupported divisor (zero, subnormal, inf, NaN, reciprocal not normal, zl underflows, or the
 *              significand fails the per-divisor check): use real division for every x.
 *   EFD_EXACT  y is a power of two: q = x * zh is exact division for EVERY x (no guard at all).
 *   EFD_FMA    q = fma(x, zh, x*zl) equals x / y for every finite x with tlo <= |x| < thi.
 *              same_sign != 0  additionally guarantees the kernel is right for x = +-0, +-inf and NaN.
 *              Otherwise +-0 and +-inf need the "special lane" value (x with its sign flipped if y < 0).
 */
#ifndef EXACT_FDIV_H
#define EXACT_FDIV_H
#include <math.h>
#include <float.h>
#include <stdint.h>
#include <string.h>

enum { EFD_DIV = 0, EFD_EXACT = 1, EFD_FMA = 2 };

typedef struct { double y, zh, zl, tlo, thi; int mode, same_sign; uint64_t bad_sig; } efd64_t;
typedef struct { float  y, zh, zl, tlo, thi; int mode, same_sign; uint32_t bad_sig; } efd32_t;

/* inverse of odd a modulo 2^64 (Newton) */
static inline uint64_t efd_inv64(uint64_t a) {
    uint64_t x = a;                     /* correct to 3 bits */
    for (int i = 0; i < 6; i++) x *= 2 - a * x;
    return x;
}

/* ---- binary64 ---- */
/* Returns 0 if Algorithm 2 is exact for every x (unbounded-exponent model) for the 53-bit significand Y,
 * else the unique failing significand X.  Theorem A: the only candidates are X < Y with X*2^54 = B*Y -+ 1. */
static inline uint64_t efd64_bad_significand(uint64_t Y) {
    if ((Y & 1) == 0) return 0;
    const int n1 = 54;                                   /* p + 1 */
    const uint64_t mask = ((uint64_t)1 << n1) - 1;
    uint64_t P = efd_inv64(Y) & mask;                    /* P*Y == 1 mod 2^54 */
    double ym = (double)Y;                               /* exact, in [2^52, 2^53) */
    double zh = 1.0 / ym, rho = fma(-ym, zh, 1.0), zl = rho / ym;
    for (int k = 0; k < 2; k++) {
        uint64_t B = k ? (mask + 1 - P) : P;             /* P- then P+ */
        unsigned __int128 t = (unsigned __int128)B * Y;
        uint64_t X = (uint64_t)((k ? t + 1 : t - 1) >> n1);
        if (X >= ((uint64_t)1 << 52) && X < Y) {
            double x = (double)X;
            if (fma(x, zh, x * zl) != x / ym) return X;
        }
    }
    return 0;
}

static inline void efd64_setup(efd64_t *c, double y) {
    memset(c, 0, sizeof *c);
    c->y = y; c->mode = EFD_DIV;
    if (!isnormal(y)) return;
    double zh = 1.0 / y;
    if (!isnormal(zh)) return;
    double rho = fma(-y, zh, 1.0);                       /* exact */
    c->zh = zh;
    if (rho == 0.0) { c->mode = EFD_EXACT; c->same_sign = 1; c->tlo = 0; c->thi = INFINITY; return; }
    double zl = rho / y;
    if (!(fabs(zl) >= 2 * DBL_MIN)) return;              /* zl must not have underflowed */
    int e;
    uint64_t Y = (uint64_t)ldexp(frexp(fabs(y), &e), 53);
    c->bad_sig = efd64_bad_significand(Y);
    if (c->bad_sig) return;
    c->zl = zl;
    c->same_sign = (signbit(zl) == signbit(zh));
    (void)frexp(fabs(zl), &e);                           /* |zl| = m * 2^e, m in [0.5, 1) */
    /* smallest power of two T with T*|zl| >= DBL_MIN: 2^(-1021-e), at least the smallest subnormal */
    c->tlo = (-1021 - e < -1074) ? 0x1p-1074 : ldexp(1.0, -1021 - e);
    /* x*zl must not overflow: for |x| < 2^(1023-e) we have |x*zl| < 2^1023 */
    c->thi = (e <= 0) ? INFINITY : ldexp(1.0, 1023 - e);
    c->mode = EFD_FMA;
}

/* scalar reference: bit-identical to x / c->y for every x */
static inline double efd64_div(const efd64_t *c, double x) {
    if (c->mode == EFD_EXACT) return x * c->zh;
    if (c->mode == EFD_FMA) {
        double a = fabs(x);
        if (a >= c->tlo && a < c->thi) return fma(x, c->zh, x * c->zl);
    }
    return x / c->y;
}

/* ---- binary32 ---- */
static inline uint32_t efd32_bad_significand(uint32_t Y) {
    if ((Y & 1) == 0) return 0;
    const int n1 = 25;
    const uint64_t mask = ((uint64_t)1 << n1) - 1;
    uint64_t P = efd_inv64(Y) & mask;
    float ym = (float)Y;
    float zh = 1.0f / ym, rho = fmaf(-ym, zh, 1.0f), zl = rho / ym;
    for (int k = 0; k < 2; k++) {
        uint64_t B = k ? (mask + 1 - P) : P;
        uint64_t t = B * Y;
        uint64_t X = (k ? t + 1 : t - 1) >> n1;
        if (X >= ((uint64_t)1 << 23) && X < Y) {
            float x = (float)X;
            if (fmaf(x, zh, x * zl) != x / ym) return (uint32_t)X;
        }
    }
    return 0;
}

static inline void efd32_setup(efd32_t *c, float y) {
    memset(c, 0, sizeof *c);
    c->y = y; c->mode = EFD_DIV;
    if (!isnormal(y)) return;
    float zh = 1.0f / y;
    if (!isnormal(zh)) return;
    float rho = fmaf(-y, zh, 1.0f);
    c->zh = zh;
    if (rho == 0.0f) { c->mode = EFD_EXACT; c->same_sign = 1; c->tlo = 0; c->thi = INFINITY; return; }
    float zl = rho / y;
    if (!(fabsf(zl) >= 2 * FLT_MIN)) return;
    int e;
    uint32_t Y = (uint32_t)ldexpf(frexpf(fabsf(y), &e), 24);
    c->bad_sig = efd32_bad_significand(Y);
    if (c->bad_sig) return;
    c->zl = zl;
    c->same_sign = (signbit(zl) == signbit(zh));
    (void)frexpf(fabsf(zl), &e);
    c->tlo = (-125 - e < -149) ? 0x1p-149f : ldexpf(1.0f, -125 - e);
    c->thi = (e <= 0) ? INFINITY : ldexpf(1.0f, 127 - e);
    c->mode = EFD_FMA;
}

static inline float efd32_div(const efd32_t *c, float x) {
    if (c->mode == EFD_EXACT) return x * c->zh;
    if (c->mode == EFD_FMA) {
        float a = fabsf(x);
        if (a >= c->tlo && a < c->thi) return fmaf(x, c->zh, x * c->zl);
    }
    return x / c->y;
}
#endif
