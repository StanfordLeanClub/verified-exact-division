/* exact_fdiv_env.h — environment checks for exact_fdiv.h.
 *
 * Kept in a separate file so that the header the tests were run against is unchanged.
 * The theorems behind exact_fdiv.h assume: no excess precision (FLT_EVAL_METHOD == 0), the default
 * round-to-nearest-even mode both at setup time and when the kernel runs, a correctly rounded fma, and
 * gradual underflow (no flush-to-zero / denormals-are-zero modes).
 * The per-divisor check itself is evaluated in hardware arithmetic, so it inherits all of these.
 * Callers that cannot guarantee these statically should use the *_checked setups below; they demote the
 * divisor to plain division (EFD_DIV) when the environment is not the assumed one.
 * The kernel must also not be used where the inexact flag is observed (it is raised when x / y is exact).
 */
#ifndef EXACT_FDIV_ENV_H
#define EXACT_FDIV_ENV_H
#include <fenv.h>
#include <float.h>
#include "exact_fdiv.h"

#if defined(FLT_EVAL_METHOD) && FLT_EVAL_METHOD != 0
#error "exact_fdiv.h requires FLT_EVAL_METHOD == 0 (no excess precision)"
#endif

/* 1 if rounding is to nearest and fma is a single-rounding fused operation on two discriminating inputs
 * (a two-rounding x*y+z returns 0 on both). */
static inline int efd_env_ok(void) {
    if (fegetround() != FE_TONEAREST) return 0;
    volatile double a = 0x1.0000000000001p0, c = -0x1.0000000000002p0;   /* a*a = 1 + 2^-51 + 2^-104 */
    if (fma(a, a, c) != 0x1p-104) return 0;
    volatile float af = 0x1.000002p0f, cf = -0x1.000004p0f;              /* af*af = 1 + 2^-22 + 2^-46 */
    if (fmaf(af, af, cf) != 0x1p-46f) return 0;
    /* flush-to-zero / denormals-are-zero (e.g. x86 MXCSR FTZ/DAZ) are outside IEEE semantics */
    volatile double sub = 0x1p-1060;
    if (sub * 0x1p-10 != 0x1p-1070) return 0;            /* FTZ: subnormal result flushed */
    if (sub * 2.0 != 0x1p-1059) return 0;                  /* DAZ: subnormal operand read as 0 */
    volatile float subf = 0x1p-140f;
    if (subf * 0x1p-5f != 0x1p-145f || subf * 2.0f != 0x1p-139f) return 0;
    return 1;
}

static inline void efd64_setup_checked(efd64_t *c, double y) {
    efd64_setup(c, y);
    if (!efd_env_ok()) c->mode = EFD_DIV;
}

static inline void efd32_setup_checked(efd32_t *c, float y) {
    efd32_setup(c, y);
    if (!efd_env_ok()) c->mode = EFD_DIV;
}
#endif
