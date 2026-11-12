/* Separate translation unit: test the actual public header, with no LTO. */
#include "div3_tight.h"
__attribute__((noinline)) void acceptance_sut(float *d, const float *s, size_t n) {
    div3_tight_array(d, s, n);
}
__attribute__((noinline)) void acceptance_hardware(float *d, const float *s, size_t n) {
    size_t i = 0;
    for (; n-i >= 8; i += 8)
        _mm256_storeu_ps(d+i, _mm256_div_ps(_mm256_loadu_ps(s+i), _mm256_set1_ps(3.0f)));
    for (; i < n; ++i) d[i] = s[i] / 3.0f;
}
