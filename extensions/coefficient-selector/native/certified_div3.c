/* The separately compiled, artifact-checked entry point. */
#include "div3_tight.h"
__attribute__((sysv_abi,noinline))
void certified_div3(float *dst, const float *src, size_t n) {
    div3_tight_array(dst,src,n);
}
