/* Native confirmation (hardware fma and division) of the binary64 witnesses in results/witnesses_binary64.json:
 * inputs on which the UNGUARDED kernel fma(x, zh, x*zl) differs from x / y, one per guard of Theorem B,
 * and confirmation that the guarded scalar reference efd64_div returns x / y on each of them.
 * Build: gcc -O2 -mfma -ffp-contract=off witness_check.c -lm */
#include <stdio.h>
#include "exact_fdiv.h"
static uint64_t bits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static int same(double a, double b) { return (a != a && b != b) || bits(a) == bits(b); }
static int one(const char *what, double x, double y) {
    volatile double yy = y, xx = x;
    double zh = 1.0 / yy, rho = fma(-yy, zh, 1.0), zl = rho / yy;
    double rawq = fma(xx, zh, xx * zl), q = xx / yy;
    efd64_t c; efd64_setup(&c, yy);
    double g = efd64_div(&c, xx);
    printf("%-46s y=%-24a x=%-26a raw=%-26a div=%-26a raw%sdiv  guarded%sdiv  (mode=%d same_sign=%d tlo=%a thi=%a)\n",
           what, y, x, rawq, q, same(rawq, q) ? "==" : "!=", same(g, q) ? "==" : "!=", c.mode, c.same_sign, c.tlo, c.thi);
    return !same(rawq, q) && same(g, q);
}
int main(void) {
    int ok = 1;
    ok &= one("tiny x, y=10", 0x0.0000000003f39p-1022, 10.0);
    ok &= one("tiny x, y=3", 0x1.abe96e4b06ce6p-1021, 3.0);
    ok &= one("tiny x, y=255", 0x1.1a207cc667e97p-1017, 255.0);
    ok &= one("tiny x, y=0.1", 0x0.a8ea3291e952ap-1022, 0.1);
    ok &= one("x=-0, zl opposite sign, y=10", -0.0, 10.0);
    ok &= one("x=+inf, zl opposite sign, y=10", INFINITY, 10.0);
    ok &= one("x*zl overflows, zl opposite sign", 0x1p+1000, 0x1.4p-997);
    ok &= one("significand rejected by the check", 0x1.4540e56da1dacp+52, 0x1.ee635506bf2efp+52);
    ok &= one("S2: zl underflowed (referee)", 0x1.15ba2177219d3p+23, 0x1.8p+1020);
    ok &= one("S1: zh subnormal (referee)", 0x1.e4f40a499abe6p+1013, 0x1.8p+1023);
    printf("%s\n", ok ? "ALL WITNESSES CONFIRMED: raw kernel wrong, guarded reference right" : "SOME WITNESS NOT CONFIRMED");
    return !ok;
}
