"""binary64 witnesses for every guard of Theorem B (exact model; confirm natively with native/witness_check.c)."""
from fractions import Fraction as F
import random, struct, json
from ieee_model import Fmt, setup, raw, div, mul, fma, val, NAN
f = Fmt(53, -1074, 971)
def fromd(d):
    if d != d: return NAN
    if d in (float('inf'), float('-inf')): return ('inf', 1 if d > 0 else -1)
    s = -1 if struct.pack('>d', d)[0] & 0x80 else 1
    return ('fin', s, abs(F(d)))
def tod(v):
    if v == NAN: return float('nan')
    if v[0] == 'inf': return v[1] * float('inf')
    x = float(v[2]); return -x if v[1] < 0 else x
def hx(v): return tod(v).hex()
out = []
random.seed(1)
# 1. tiny x: x*zl underflows; y = 10
for yv in (10.0, 3.0, 255.0, 0.1):
    y = fromd(yv); st = setup(f, y)
    zh, zl, T, ok2, Thi = st
    found = None
    for trial in range(200000):
        e = random.randint(-1074, -1074 + 60) if trial % 2 else random.randint(-1022, -960)
        m = random.getrandbits(53) | (1 << 52)
        xv = F(m) * F(2) ** (e - 52)
        if xv < F(2) ** -1074: continue
        x = f.rnd(1, xv)
        if x[2] == 0 or x[2] >= T: continue
        if raw(f, x, st) != div(f, x, y):
            found = x; break
    out.append(dict(kind='tiny x (below tlo): raw kernel != x/y', y=yv, tlo=float(T).hex(), x=hx(found) if found else None,
                    raw=hx(raw(f, found, st)) if found else None, div=hx(div(f, found, y)) if found else None,
                    same_sign=(zl[1] == zh[1])))
# 2. signed zero and infinity with opposite-signed zl (y = 10)
y = fromd(10.0); st = setup(f, y)
for xv in (-0.0, float('inf')):
    x = fromd(xv)
    out.append(dict(kind='special value, zl opposite sign', y=10.0, x=str(xv), raw=str(tod(raw(f, x, st))), div=str(tod(div(f, x, y))),
                    zh=hx(st[0]), zl=hx(st[1])))
# 3. overflow of x*zl with opposite-signed zl: tiny y
yv = 10.0 * 2.0 ** -1000
y = fromd(yv); st = setup(f, y)
zh, zl, T, ok2, Thi = st
xv = 2.0 ** 1000
x = fromd(xv)
out.append(dict(kind='x*zl overflows (x >= thi), zl opposite sign', y=yv.hex(), x=xv.hex(), thi=float(Thi).hex() if Thi else None,
                zl=hx(zl), raw=str(tod(raw(f, x, st))), div=str(tod(div(f, x, y)))))
# 4. a divisor rejected by the significand check, with its failing x
import sys
sys.path.insert(0, '.')
from checker import bad_x
random.seed(7)
while True:
    Y = random.getrandbits(53) | (1 << 52) | 1
    b = bad_x(Y, 53)
    if b:
        out.append(dict(kind='significand check rejects', y=float(Y).hex(), x=float(b[0]).hex(),
                        raw=hx(raw(f, fromd(float(b[0])), setup(f, fromd(float(Y))))), div=hx(div(f, fromd(float(b[0])), fromd(float(Y))))))
        break
for o in out: print(o)
json.dump(out, open('../results/witnesses_binary64.json', 'w'), indent=1)
