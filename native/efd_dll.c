/* Windows DLL exposing the kernels to Python/ctypes for an in-process comparison with NumPy's true_divide.
 * Build (clang, MSVC target):
 *   clang -O2 -mavx2 -mfma -ffp-contract=off -shared -o efd.dll efd_dll.c */
#include "efd_kernels.h"
#define EXPORT __declspec(dllexport)
EXPORT void efd64_array(double *dst, const double *src, size_t n, double y) { efd64_div_array(dst, src, n, y); }
EXPORT void efd32_array(float *dst, const float *src, size_t n, float y) { efd32_div_array(dst, src, n, y); }
EXPORT void vdiv64_array(double *dst, const double *src, size_t n, double y) { div64_array(dst, src, n, y); }
EXPORT void vdiv32_array(float *dst, const float *src, size_t n, float y) { div32_array(dst, src, n, y); }
EXPORT int efd64_mode(double y) { efd64_t c; efd64_setup(&c, y); return c.mode * 10 + c.same_sign; }
EXPORT int efd32_mode(float y) { efd32_t c; efd32_setup(&c, y); return c.mode * 10 + c.same_sign; }
