# Toy IEEE format (p bits, exponents emin..emax of the ulp) with subnormals, overflow to inf.
# Exhaustive over all finite positive x, all normal positive y: where does q=fma(x,zh,x*zl) differ from RN(x/y)?
from fractions import Fraction as F
import sys, collections
p, emin, emax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])          # value = m * 2^e, e in [emin, emax], m < 2^p ; minnormal = 2^(p-1+emin)
INF = 'inf'
def rn(t):
    if t == 0: return F(0)
    a = abs(t); n, d = a.numerator, a.denominator
    e = n.bit_length() - d.bit_length() - p
    while a >= F(2)**(e+p): e += 1
    while a < F(2)**(e+p-1): e -= 1
    if e < emin: e = emin
    m = a / F(2)**e
    fl = m.numerator // m.denominator; r = m - fl
    if r > F(1,2) or (r == F(1,2) and fl % 2 == 1): fl += 1
    v = fl * F(2)**e
    if v >= F(2)**(emax + p): return INF
    return v if t > 0 else -v
def floats():
    out = []
    for e in range(emin, emax+1):
        for m in range(2**(p-1) if e > emin else 1, 2**p):
            out.append(F(m) * F(2)**e)
    return out
FL = floats()
minnormal = F(2)**(p-1+emin)
def lg(v):  # floor log2
    n, d = v.numerator, v.denominator
    e = n.bit_length() - d.bit_length()
    if F(2)**e > v: e -= 1
    return e
stats = collections.Counter(); regions = collections.Counter(); ybad_normal = set(); ny = 0
for y in FL:
    if y < minnormal: continue
    inv = 1 / y
    zh = rn(inv)
    if zh == INF or zh < minnormal: continue
    zl = rn(inv - zh)
    ny += 1
    for x in FL:
        qt = rn(x / y)
        t = rn(x * zl)
        qa = INF if t == INF else rn(x * zh + t)
        if qa != qt:
            xl = x * abs(zl)
            if zl != 0 and abs(zl) < minnormal: reg = 'zl subnormal'
            elif qt == INF or qa == INF: reg = 'overflow-edge'
            elif (x / y) < minnormal: reg = 'q subnormal'
            elif zl != 0 and xl < minnormal: reg = 'x*zl subnormal, q normal (q exp above min: %d)' % (lg(x / y) - (p-1+emin))
            else: reg = 'NORMAL'; ybad_normal.add(y)
            regions[reg.split(' (')[0]] += 1
            stats[reg] += 1
print('format p=%d emin=%d emax=%d; divisors tested %d' % (p, emin, emax, ny))
for k, v in sorted(regions.items()): print('  ', k, v)
print('divisors with a failure in the fully-normal region:', len(ybad_normal))
ks = sorted(k for k in stats if 'q exp above' in k)
print('  failures by distance of q exponent above min-normal exponent:', {int(k.split('min: ')[1][:-1]): stats[k] for k in ks})
