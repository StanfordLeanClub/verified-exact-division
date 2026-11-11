# Exact model of radix-2 precision-p floats with unbounded exponent.
# Test: for each divisor mantissa Y in [2^(p-1), 2^p), is q = RN(x*zh + RN(x*zl)) == RN(x/y) for all x mantissas?
from fractions import Fraction as F
import sys
def rn(t, p):
    """round-to-nearest-even of Fraction t to p significant bits (unbounded exponent)."""
    if t == 0: return F(0)
    s = 1 if t > 0 else -1
    a = abs(t)
    # find e with 2^(p-1) <= a/2^e < 2^p
    n, d = a.numerator, a.denominator
    e = n.bit_length() - d.bit_length() - p
    while F(n, d) / F(2)**e >= 2**p: e += 1
    while F(n, d) / F(2)**e < 2**(p-1): e -= 1
    m = F(n, d) / F(2)**e
    fl = m.numerator // m.denominator
    r = m - fl
    if r > F(1,2) or (r == F(1,2) and fl % 2 == 1): fl += 1
    return s * fl * F(2)**e
def rz(t, p):
    if t == 0: return F(0)
    s = 1 if t > 0 else -1
    a = abs(t); n, d = a.numerator, a.denominator
    e = n.bit_length() - d.bit_length() - p
    while F(n, d) / F(2)**e >= 2**p: e += 1
    while F(n, d) / F(2)**e < 2**(p-1): e -= 1
    m = F(n, d) / F(2)**e
    return s * (m.numerator // m.denominator) * F(2)**e
def test(p, mode):
    ok = 0; bad = 0; worst = []
    for Y in range(2**(p-1), 2**p):
        y = F(Y)
        inv = 1 / y
        zh = rn(inv, p) if mode == 'rn' else rz(inv, p)
        zl = rn(inv - zh, p)
        fails = 0
        for X in range(2**(p-1), 2**p):
            x = F(X)
            q = rn(x*zh + rn(x*zl, p), p)
            if q != rn(x / y, p): fails += 1
        if fails: bad += 1; worst.append((Y, fails))
        else: ok += 1
    return ok, bad, worst
for p in map(int, sys.argv[2:]):
    ok, bad, worst = test(p, sys.argv[1])
    print(p, sys.argv[1], 'ok', ok, 'bad', bad, 'frac_bad', round(bad/(ok+bad), 4), 'maxfails', max([w[1] for w in worst], default=0), 'examples', worst[:6])
