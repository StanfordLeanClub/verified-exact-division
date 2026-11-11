"""Exact model of an IEEE-754 binary format (precision p, ulp exponents emin..emax, subnormals, signed zeros,
infinities, NaN, round-to-nearest-even) and of the guarded division-free kernel.

Values: ('nan',) | ('inf', s) | ('fin', s, Fraction m>=0)   with s in {+1,-1}  (so ('fin', -1, 0) is -0).

Full-range claim tested here exhaustively on small formats (THEOREM.md, Theorem B):
  setup(y) returns None (unsupported: use real division) or (zh, zl, T, ok2).
  If ok2 (the significand of y passes the Theorem-A check) then for EVERY x of the format
      guarded(x) == x / y   bit for bit (sign of zero included, NaN as NaN),
  where guarded(x) = fma(x, zh, x*zl)            if T <= |x| < inf
                   = x with sign flipped by y    if x is 0, inf or NaN      ("special lanes")
                   = x / y                        if 0 < |x| < T            (fallback, real division)
                   = x / y                        if |x| >= Thi (only when |zl| > 1: x*zl could overflow)
  and T is a power of two with T*|zl| >= smallest normal (strict mode, also flag-exact for underflow),
  or with T/|y| >= 2^(emin+2p) (loose mode).
"""
from fractions import Fraction as F
import sys, json, collections


class Fmt:
    def __init__(s, p, emin, emax):
        s.p, s.emin, s.emax = p, emin, emax
        s.minnormal = F(2) ** (emin + p - 1)
        s.maxfloat = (2 ** p - 1) * F(2) ** emax
        s.ovf = (2 ** (p + 1) - 1) * F(2) ** (emax - 1)      # values >= this round to inf

    def rnd(s, sign, a):
        """RN-even of exact nonnegative Fraction a with given sign"""
        if a == 0:
            return ('fin', sign, F(0))
        if a >= s.ovf:
            return ('inf', sign)
        n, d = a.numerator, a.denominator
        e = n.bit_length() - d.bit_length() - s.p
        if n * 2 ** max(0, -e) >= d * 2 ** max(0, e) * 2 ** s.p:
            e += 1
        if n * 2 ** max(0, -e) < d * 2 ** max(0, e) * 2 ** (s.p - 1):
            e -= 1
        if e < s.emin:
            e = s.emin
        num = n * 2 ** max(0, -e)
        den = d * 2 ** max(0, e)
        fl, rem = divmod(num, den)
        if 2 * rem > den or (2 * rem == den and fl & 1):
            fl += 1
        return ('fin', sign, fl * F(2) ** e)

    def rsigned(s, t):
        return s.rnd(1 if t > 0 else -1, abs(t))

    def all_finite(s):
        out = []
        for e in range(s.emin, s.emax + 1):
            for m in range(2 ** (s.p - 1) if e > s.emin else 0, 2 ** s.p):
                v = m * F(2) ** e
                out.append(('fin', 1, v))
                out.append(('fin', -1, v))
        return out

    def all_values(s):
        return s.all_finite() + [('inf', 1), ('inf', -1), ('nan',)]


NAN = ('nan',)


def sgn(v):
    return v[1]


def val(v):
    return v[1] * v[2]


def iszero(v):
    return v[0] == 'fin' and v[2] == 0


def mul(f, a, b):
    if a == NAN or b == NAN:
        return NAN
    s = sgn(a) * sgn(b)
    if a[0] == 'inf' or b[0] == 'inf':
        if iszero(a) or iszero(b):
            return NAN
        return ('inf', s)
    return f.rnd(s, a[2] * b[2])


def div(f, a, b):
    if a == NAN or b == NAN:
        return NAN
    s = sgn(a) * sgn(b)
    if a[0] == 'inf':
        return NAN if b[0] == 'inf' else ('inf', s)
    if b[0] == 'inf':
        return ('fin', s, F(0))
    if b[2] == 0:
        return NAN if a[2] == 0 else ('inf', s)
    return f.rnd(s, a[2] / b[2])


def fma(f, a, b, c):
    """a*b + c with a single rounding"""
    if a == NAN or b == NAN or c == NAN:
        return NAN
    ps = sgn(a) * sgn(b)
    if a[0] == 'inf' or b[0] == 'inf':
        if iszero(a) or iszero(b):
            return NAN
        if c[0] == 'inf' and sgn(c) != ps:
            return NAN
        return ('inf', ps)
    if c[0] == 'inf':
        return c
    prod = ps * a[2] * b[2]
    t = prod + val(c)
    if t == 0:
        # exact zero result under RN: two zeros of the same sign keep it, everything else is +0
        if a[2] * b[2] == 0 and c[2] == 0 and ps == sgn(c):
            return ('fin', ps, F(0))
        return ('fin', 1, F(0))
    return f.rsigned(t)


def neg(v):
    return v if v == NAN else (v[0], -v[1]) + v[2:]


def is_normal(f, v):
    return v[0] == 'fin' and v[2] >= f.minnormal


# ---------- unbounded-model significand check (Theorem A) ----------
def rn_unb(t, p):
    if t == 0:
        return F(0)
    sg = 1 if t > 0 else -1
    a = abs(t)
    n, d = a.numerator, a.denominator
    e = n.bit_length() - d.bit_length() - p
    if n * 2 ** max(0, -e) >= d * 2 ** max(0, e) * 2 ** p:
        e += 1
    if n * 2 ** max(0, -e) < d * 2 ** max(0, e) * 2 ** (p - 1):
        e -= 1
    num = n * 2 ** max(0, -e)
    den = d * 2 ** max(0, e)
    fl, rem = divmod(num, den)
    if 2 * rem > den or (2 * rem == den and fl & 1):
        fl += 1
    return sg * F(fl) * F(2) ** e


def sig_ok(Y, p):
    """True iff Algorithm 2 is exact for every x in the unbounded model, for significand Y"""
    if Y % 2 == 0 or Y == 1:
        return True
    inv = F(1, Y)
    zh = rn_unb(inv, p)
    zl = rn_unb(inv - zh, p)
    i2 = pow(2 ** (p + 1), -1, Y)
    for s in (1, -1):
        X = (s * i2) % Y
        if 2 ** (p - 1) <= X < Y:
            if rn_unb(X * zh + rn_unb(X * zl, p), p) != rn_unb(F(X, Y), p):
                return False
    return True


def significand(f, v):
    """integer significand in [2^(p-1), 2^p) of a normal value"""
    m = v[2]
    while m < 2 ** (f.p - 1):
        m *= 2
    while m >= 2 ** f.p:
        m /= 2
    assert m.denominator == 1
    return m.numerator


# ---------- setup and guarded kernel ----------
def setup(f, y, strict=True):
    """Uses only operations of the format itself (as a C implementation would)."""
    if y == NAN or y[0] == 'inf' or not is_normal(f, y):
        return None
    one = ('fin', 1, F(1))
    zh = div(f, one, y)
    if not is_normal(f, zh):
        return None
    rho = fma(f, neg(y), zh, one)                 # exact: 1 - y*zh
    assert val(rho) == 1 - val(y) * val(zh), 'rho not exact'
    zl = div(f, rho, y)
    if rho[2] != 0 and zl[2] < 2 * f.minnormal:
        return None                               # zl must be a rounding in the unbounded sense (not underflowed)
    ok2 = sig_ok(significand(f, y), f.p)
    if zl[2] == 0:
        T = F(0)
    elif strict:
        T = f.minnormal / zl[2]
    else:
        T = F(2) ** (f.emin + 2 * f.p) * y[2]
    Tp = F(0)
    if T > 0:
        Tp = F(2) ** f.emin                       # smallest subnormal
        while Tp < T:
            Tp *= 2                               # round up to a power of two
    # upper guard: x*zl must not overflow (matters only when |zl| > 1, i.e. tiny |y|)
    Thi = None
    if zl[2] > 1:
        Thi = F(2) ** (f.emax + f.p)
        while Thi * zl[2] >= f.ovf:
            Thi /= 2
    return zh, zl, Tp, ok2, Thi


def guarded(f, x, y, st):
    zh, zl, T, ok2, Thi = st
    if x == NAN:
        return NAN, 'special'
    if x[0] == 'inf' or x[2] == 0:
        return (x[0], sgn(x) * sgn(y)) + x[2:], 'special'
    if x[2] < T:
        return div(f, x, y), 'fallback'
    if Thi is not None and x[2] >= Thi:
        return div(f, x, y), 'fallback-high'
    return fma(f, x, zh, mul(f, x, zl)), 'fast'


def raw(f, x, st):
    zh, zl = st[0], st[1]
    return fma(f, x, zh, mul(f, x, zl))


if __name__ == '__main__':
    p, emin, emax = map(int, sys.argv[1:4])
    strict = (len(sys.argv) < 5 or sys.argv[4] != 'loose')
    f = Fmt(p, emin, emax)
    xs = f.all_values()
    ys = f.all_values()
    stat = collections.Counter()
    nbad = 0
    rawstat = collections.Counter()
    for y in ys:
        st = setup(f, y, strict)
        if st is None:
            stat['y unsupported'] += 1
            continue
        if not st[3]:
            stat['y fails significand check'] += 1
            continue
        stat['y supported'] += 1
        same = iszero(st[1]) or (sgn(st[0]) == sgn(st[1]))
        for x in xs:
            want = div(f, x, y)
            got, path = guarded(f, x, y, st)
            stat['x ' + path] += 1
            if got != want:
                nbad += 1
                if nbad < 10:
                    print('MISMATCH', x, y, got, want, path)
            if path != 'fast':
                r = raw(f, x, st)
                key = path + (' | zl same sign' if same else ' | zl opposite sign')
                rawstat[key + (' | raw kernel right' if r == want else ' | raw kernel WRONG')] += 1
    print('format p=%d emin=%d emax=%d strict=%s: %d values' % (p, emin, emax, strict, len(xs)))
    for k in sorted(stat):
        print('  %-32s %d' % (k, stat[k]))
    print('  MISMATCHES guarded vs division: %d' % nbad)
    for k in sorted(rawstat):
        print('  unguarded kernel on guarded lanes: %-60s %d' % (k, rawstat[k]))
    name = '../results/ieee_model_p%d_%d_%d_%s.json' % (p, emin, emax, 'strict' if strict else 'loose')
    json.dump(dict(p=p, emin=emin, emax=emax, strict=strict, stats=dict(stat), mismatches=nbad,
                   raw_on_guarded_lanes=dict(rawstat)), open(name, 'w'), indent=1)
