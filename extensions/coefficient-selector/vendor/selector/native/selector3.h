#ifndef SELECTOR3_H
#define SELECTOR3_H
#include "../vendor/native/efd_kernels.h"

/* Offline-selected binary32 coefficients. RNE, fused FMA, FTZ/DAZ disabled.
 * This does not run the general exact-rational selector at runtime.
 * The Lean theorem covers normalized unbounded values; the complete guarded
 * native value behavior is separately checked exhaustively. Flags and NaN
 * payloads are not part of that native comparison. */
static inline void selector3_setup(efd32_t *c, float y) {
    if (y != 3.0f) { efd32_setup(c, y); return; }
    *c = (efd32_t){3.0f, 0x1.555554p-2f, 0x1.555556p-26f,
                  0x1p-100f, INFINITY, EFD_FMA, 1, 0};
}
#endif
