// Exhaustive check over all float32 mantissas x in [1,2) for sampled divisors y in [1,2):
//   A2: q = fma(x, zh, x*zl), zh = RN(1/y), zl = RN(1/y - zh)   (computed exactly via double/long double)
//   A2z: same with zh = RZ(1/y) so that zl >= 0
//   A3: q0 = x*zh; r = fma(-q0, y, x); q = fma(r, zh, q0)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
static uint64_t s = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void){ s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
int main(int argc, char **argv){
  int N = argc > 1 ? atoi(argv[1]) : 1000;
  long badA2 = 0, badA2z = 0, badA3 = 0, bothbad = 0;
  long totfA2 = 0, totfA2z = 0, totfA3 = 0;
  for (int it = 0; it < N; it++){
    uint32_t Y = (1u << 23) | (uint32_t)(rnd() & 0x7FFFFF);
    if (it < 64) Y = (1u << 23) + (2*it + 1) * (1u << 17) ; // some short mantissas
    float y = (float)Y / 8388608.0f;
    // exact reciprocal to ~64 bits
    long double inv = 1.0L / (long double)y;
    float zh = (float)inv;               // RN
    float zl = (float)(inv - (long double)zh);
    float zhz = zh; if ((long double)zhz > inv) zhz = nextafterf(zhz, 0.0f);
    float zlz = (float)(inv - (long double)zhz);
    long fA2 = 0, fA2z = 0, fA3 = 0;
    for (uint32_t X = 1u << 23; X < (1u << 24); X++){
      float x = (float)X / 8388608.0f;
      float q = x / y;
      float a2 = fmaf(x, zh, x * zl);
      float a2z = fmaf(x, zhz, x * zlz);
      float q0 = x * zh; float r = fmaf(-q0, y, x); float a3 = fmaf(r, zh, q0);
      fA2 += (a2 != q); fA2z += (a2z != q); fA3 += (a3 != q);
    }
    badA2 += fA2 != 0; badA2z += fA2z != 0; badA3 += fA3 != 0; bothbad += (fA2 != 0 && fA2z != 0);
    totfA2 += fA2; totfA2z += fA2z; totfA3 += fA3;
    if (it < 3 || (fA3 && badA3 < 4)) printf("Y=%u zl=%g zlz=%g fails A2=%ld A2z=%ld A3=%ld\n", Y, zl, zlz, fA2, fA2z, fA3);
  }
  printf("N=%d  divisors with any failure: A2(rn)=%ld  A2(rz)=%ld  A3=%ld  both A2 variants=%ld\n", N, badA2, badA2z, badA3, bothbad);
  printf("total failing x: A2=%ld A2z=%ld A3=%ld\n", totfA2, totfA2z, totfA3);
  return 0;
}
