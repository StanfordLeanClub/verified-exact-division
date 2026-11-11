"""Exact per-divisor decision procedure for Algorithm 2 (unbounded-exponent model, precision p).

  zh = RN(1/y), zl = RN(1/y - zh), q = RN(x*zh + RN(x*zl))   versus   RN(x/y)

Claim (THEOREM.md, Theorem A): with x = X, y = Y integer significands in [2^(p-1), 2^p), q can differ from RN(x/y)
only if Y is odd, X < Y and X * 2^(p+1) = B*Y + s for some integer B and s in {+1, -1}.  For each sign there is at
most one such X (X = s * (2^(p+1))^-1 mod Y), so the check is two modular inverses and two exact evaluations.
This file implements that and validates it against brute force."""
from fractions import Fraction as F
import sys, json

def rn(t, p):
    """round-to-nearest-even of a Fraction to p significant bits, unbounded exponent"""
    if t == 0: return F(0)
    sg = 1 if t > 0 else -1; a = abs(t)
    n, d = a.numerator, a.denominator
    e = n.bit_length() - d.bit_length() - p
    if n * 2 ** max(0, -e) >= d * 2 ** max(0, e) * 2 ** p: e += 1
    if n * 2 ** max(0, -e) < d * 2 ** max(0, e) * 2 ** (p - 1): e -= 1
    num = n * 2 ** max(0, -e); den = d * 2 ** max(0, e)
    fl, rem = divmod(num, den)
    if 2 * rem > den or (2 * rem == den and fl & 1): fl += 1
    return sg * F(fl) * F(2) ** e

def setup(Y, p):
    inv = F(1, Y); zh = rn(inv, p); zl = rn(inv - zh, p)
    return zh, zl

def alg2(X, zh, zl, p): return rn(X * zh + rn(X * zl, p), p)

def alg1(X, Y, zh, p):
    q0 = rn(X * zh, p); r = rn(X - q0 * Y, p); return rn(q0 + r * zh, p)

def candidates(Y, p):
    if Y % 2 == 0: return []
    out = []
    inv = pow(2 ** (p + 1), -1, Y) if Y > 1 else 0
    for s in (1, -1):
        X = (s * inv) % Y
        if 2 ** (p - 1) <= X < Y:
            assert (X * 2 ** (p + 1) - s) % Y == 0
            out.append(X)
    return out

def bad_x(Y, p):
    """list of significands X for which Algorithm 2 misrounds X/Y (empty list <=> exact for every x)"""
    zh, zl = setup(Y, p)
    return [X for X in candidates(Y, p) if alg2(X, zh, zl, p) != rn(F(X, Y), p)]

if __name__ == '__main__':
    res = {}
    for p in range(3, int(sys.argv[1]) + 1):
        nbad = ncand = mism = b1 = 0
        for Y in range(2 ** (p - 1), 2 ** p):
            zh, zl = setup(Y, p)
            brute = [X for X in range(2 ** (p - 1), 2 ** p) if alg2(X, zh, zl, p) != rn(F(X, Y), p)]
            fast = bad_x(Y, p)
            ncand += len(candidates(Y, p)); nbad += bool(brute)
            if brute != fast: mism += 1; print('MISMATCH', p, Y, brute, fast)
            if p <= 10 and any(alg1(X, Y, zh, p) != rn(F(X, Y), p) for X in range(2 ** (p - 1), 2 ** p)): b1 += 1
        res[p] = dict(divisors=2 ** (p - 1), bad_divisors=nbad, candidates=ncand, checker_mismatches=mism,
                      alg1_bad_divisors=(b1 if p <= 10 else None))
        print(p, res[p], flush=True)
    json.dump(res, open('../results/checker_vs_bruteforce.json', 'w'), indent=1)
