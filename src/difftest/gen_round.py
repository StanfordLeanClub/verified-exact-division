"""Rounding correspondence: Lean `rneR 53 (-1074) 971` on the exact quotient x/y vs the hardware (CPython) double x / y."""
import random, struct, math, sys
from fractions import Fraction as F
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
def rnd_double():
    while True:
        k = random.random()
        if k < 0.5:
            b = random.getrandbits(64)
        else:   # wide but controlled exponents, to hit subnormal and overflow quotients often
            b = (random.getrandbits(1) << 63) | (random.randint(1, 2046) << 52) | random.getrandbits(52)
        d = struct.unpack('<d', struct.pack('<Q', b))[0]
        if math.isfinite(d) and d != 0:
            return d
rows = []
for i in range(N):
    x, y = rnd_double(), rnd_double()
    if i % 4 == 1:     # force tiny quotients (subnormal / total underflow)
        x = math.ldexp(abs(x) / 2 ** math.frexp(abs(x))[1], -1000 - random.randint(0, 74)) * (1 if x > 0 else -1); y = math.ldexp(1.0 + random.random(), random.randint(0, 60))
    if i % 4 == 2:     # force huge quotients (overflow edge)
        x = math.ldexp(1.0 + random.random(), 1000 + random.randint(0, 23)); y = math.ldexp(1.0 + random.random(), -random.randint(0, 40))
    rows.append((x, y))
with open('pairs.txt', 'w', newline=chr(10)) as f:
    for x, y in rows:
        a, b = F(x), F(y)
        f.write(f'{a.numerator} {a.denominator} {b.numerator} {b.denominator}\n')
with open('pairs_expected.txt', 'w', newline=chr(10)) as f:
    for x, y in rows:
        q = x / y if not (abs(x / y) == math.inf and False) else 0
        if math.isinf(q): f.write(('inf -' if q < 0 else 'inf +') + '\n')
        elif q == 0: f.write(('zero -' if math.copysign(1, q) < 0 else 'zero +') + '\n')
        else:
            r = F(q); f.write(f'{r.numerator} {r.denominator}\n')
print(N)
