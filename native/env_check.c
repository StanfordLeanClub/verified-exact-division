/* smoke test of exact_fdiv_env.h: gcc -O2 -mfma -ffp-contract=off env_check.c -lm */
#include <stdio.h>
#include "exact_fdiv_env.h"
int main(void) {
    efd64_t c; efd32_t d;
    efd64_setup_checked(&c, 3.0); efd32_setup_checked(&d, 3.0f);
    printf("round-to-nearest: env_ok=%d mode64=%d mode32=%d\n", efd_env_ok(), c.mode, d.mode);
    fesetround(FE_UPWARD);
    efd64_setup_checked(&c, 3.0);
    printf("round-upward:     env_ok=%d mode64=%d (0 = falls back to division)\n", efd_env_ok(), c.mode);
    fesetround(FE_TONEAREST);
    return 0;
}
