/* reads ys64.txt / ys32.txt and prints the C verdicts as 0/1 strings (1 = accepted) */
#include <stdio.h>
#include "../../native/exact_fdiv.h"
int main(void) {
    FILE *f = fopen("ys64.txt", "r"); unsigned long long y;
    while (fscanf(f, "%llu", &y) == 1) putchar(efd64_bad_significand(y) ? '0' : '1');
    putchar('\n'); fclose(f);
    f = fopen("ys32.txt", "r");
    while (fscanf(f, "%llu", &y) == 1) putchar(efd32_bad_significand((uint32_t)y) ? '0' : '1');
    putchar('\n'); fclose(f);
    return 0;
}
