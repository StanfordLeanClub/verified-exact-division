#ifndef CERTIFIED_DIV3_API_H
#define CERTIFIED_DIV3_API_H
#include <stddef.h>
/* Dedicated, separately linked artifact, using the System V x86-64 register
 * convention even on Windows. Requires Clang, AVX2/FMA, nearest-even, gradual
 * underflow, masked FP exceptions, and valid disjoint or equal float ranges.
 * Only the byte-checked object is covered; arbitrary inline recompilation is
 * not covered. Flags and NaN payloads are not preserved. */
#ifdef __cplusplus
extern "C" {
#endif
__attribute__((sysv_abi)) void certified_div3(float *dst,const float *src,size_t n);
#ifdef __cplusplus
}
#endif
#endif
