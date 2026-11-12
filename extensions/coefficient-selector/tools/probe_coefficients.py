"""Independent exact-arithmetic exploration, NOT a formal proof or IEEE implementation.

Run: python probe_coefficients.py --toy-max 10 --samples 10000 --seed 20261110
Model: precision p, unbounded exponent, round to nearest ties to even.
The generalized checker enumerates every rounding breakpoint within a uniform
error bound of X/Y, using modular congruences. Toy checks compare this with
exhaustive enumeration; native checks are in native_probe.c.
"""
from fractions import Fraction as F
from math import gcd
import argparse
import json
from pathlib import Path
import random
import time


def pow2(e):
    return F(1 << e) if e >= 0 else F(1, 1 << -e)


def flog2(t):
    t = abs(t)
    e = t.numerator.bit_length() - t.denominator.bit_length()
    return e - (t < pow2(e))


def rn(t, p):
    t = F(t)
    if not t:
        return t
    sg = 1 if t > 0 else -1
    e = flog2(t) - p + 1
    z = abs(t) / pow2(e)
    n, r = divmod(z.numerator, z.denominator)
    return sg * (n + (2*r > z.denominator or (2*r == z.denominator and n % 2))) * pow2(e)


def neighbor(t, direction, p):
    assert t and direction in (-1, 1)
    e = flog2(t) - p + 1
    if abs(t) == pow2(flog2(t)) and (t > 0) != (direction > 0):
        e -= 1
    return t + direction * pow2(e)


def kernel(X, h, l, p):
    return rn(X*h + rn(X*l, p), p)


def error_bound(Y, h, l, p):
    P = 1 << p
    product_error = pow2(flog2((P-1)*abs(l)) - p) if l else F(0)
    return (P-1)*abs(h+l-F(1,Y)) + product_error


def nearby_inputs(Y, h, l, p):
    P = 1 << p
    E = error_bound(Y,h,l,p)
    # Ensures the pre-rounded value stays in (1/2, 2), so these two
    # breakpoint grids cover all possible changes to the rounded result.
    assert E < F(1, 2*P), (p,Y,E)
    out = set()
    for A in (P,2*P):
        bound = E*A*Y
        N = bound.numerator // bound.denominator
        g = gcd(A,Y)
        mod = Y//g
        inverse = pow(A//g, -1, mod) if mod > 1 else 0
        for n in range(-N,N+1):
            if n % g:
                continue
            # A/g is even and Y/g odd (Y < P). Therefore B is odd
            # exactly when n/g is odd. Skip before enumerating solutions:
            # the n=0 congruence can otherwise have exponentially many X.
            if not (n//g) % 2:
                continue
            residue = (n//g*inverse) % mod if mod > 1 else 0
            first = P//2 + (residue-P//2) % mod
            for X in range(first,P,mod):
                B = (A*X-n)//Y
                if B % 2:
                    out.add(X)
    return sorted(out)


def failures(Y,h,l,p):
    return [X for X in nearby_inputs(Y,h,l,p) if kernel(X,h,l,p) != rn(F(X,Y),p)]


def canonical(Y,p):
    h = rn(F(1,Y),p)
    return h,rn(F(1,Y)-h,p)


def candidates(Y,p):
    if Y % 2 == 0:
        return []
    P = 1 << p
    t = pow(2*P,-1,Y)
    return [X for X in (t,Y-t) if P//2 <= X < Y]


def variants(Y,p):
    h,l = canonical(Y,p)
    yield 'canonical',h,l
    if l:
        yield 'low_down',h,neighbor(l,-1,p)
        yield 'low_up',h,neighbor(l,1,p)
    for d,name in ((-1,'head_down'),(1,'head_up')):
        hh=neighbor(h,d,p)
        ll=rn(F(1,Y)-hh,p)
        yield name,hh,ll
        yield name+'_low_down',hh,neighbor(ll,-1,p)
        yield name+'_low_up',hh,neighbor(ll,1,p)


def record(Y,p):
    vs=list(variants(Y,p))
    bad=failures(Y,vs[0][1],vs[0][2],p)
    # Cross-check the generalized bound checker against BMR's unique candidate.
    bmr=[X for X in candidates(Y,p) if kernel(X,vs[0][1],vs[0][2],p) != rn(F(X,Y),p)]
    assert bad == bmr,(Y,p,bad,bmr)
    repairs=[]
    if bad:
        for name,h,l in vs[1:]:
            fs=failures(Y,h,l,p)
            if not fs:
                repairs.append(name)
    return bad,repairs


def toy(p):
    counts={'p':p,'divisors':1<<(p-1),'bad_canonical':0,'repair_low':0,'repair_any':0,
            'checker_brute_mismatches':0,'brute_pairs':0,'unrepaired':[], 'examples':[]}
    P=1<<p
    for Y in range(P//2,P):
        bad,repairs=record(Y,p)
        counts['bad_canonical']+=bool(bad)
        counts['repair_low']+=any(r in ('low_up','low_down') for r in repairs)
        counts['repair_any']+=bool(repairs)
        if bad and not repairs:
            counts['unrepaired'].append(Y)
        # Canonical on all Y; every proposed variant on failing Y; directed
        # head on all Y at p<=8. This validates modifications, not only BMR.
        for name,h,l in variants(Y,p):
            if name != 'canonical' and not bad and not (p<=8 and name=='head_down'):
                continue
            brute=[X for X in range(P//2,P) if kernel(X,h,l,p) != rn(F(X,Y),p)]
            predicted=failures(Y,h,l,p)
            counts['brute_pairs']+=P//2
            if brute != predicted:
                counts['checker_brute_mismatches']+=1
                raise AssertionError((p,Y,name,brute,predicted))
        if bad and len(counts['examples'])<8:
            counts['examples'].append({'Y':Y,'bad_X':bad,'repairs':repairs})
    return counts


def sampled(p,n,seed):
    rng=random.Random(seed+p)
    P=1<<p
    counts={'p':p,'divisors':n,'seed':seed+p,'bad_canonical':0,'repair_low':0,'repair_any':0,
            'unrepaired':[],'examples':[],'same_sign_canonical':0,'same_sign_canonical_safe':0,
            'same_sign_head_down_safe':0}
    for _ in range(n):
        Y=rng.randrange(P//2,P)
        h,l=canonical(Y,p)
        counts['same_sign_canonical']+=l>=0
        hd=h if l>=0 else neighbor(h,-1,p)
        ld=rn(F(1,Y)-hd,p)
        counts['same_sign_head_down_safe']+=not failures(Y,hd,ld,p)
        bad,repairs=record(Y,p)
        counts['same_sign_canonical_safe']+=l>=0 and not bad
        counts['bad_canonical']+=bool(bad)
        counts['repair_low']+=any(r in ('low_up','low_down') for r in repairs)
        counts['repair_any']+=bool(repairs)
        if bad and not repairs:
            counts['unrepaired'].append(Y)
        if bad and len(counts['examples'])<20:
            counts['examples'].append({'Y':Y,'bad_X':bad,'repairs':repairs})
    return counts


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--toy-max',type=int,default=10)
    ap.add_argument('--samples',type=int,default=10000)
    ap.add_argument('--seed',type=int,default=20261110)
    ap.add_argument('--out',default='results/coefficients.json')
    args=ap.parse_args()
    started=time.time()
    rows=[]
    out=Path(args.out)
    out.parent.mkdir(parents=True,exist_ok=True)
    for p in range(4,args.toy_max+1):
        r=toy(p);rows.append(r);print(json.dumps(r),flush=True)
        out.write_text(json.dumps({'model':'unbounded RNE; experimental checker, not Lean','rows':rows},indent=2))
    for p in (24,53):
        r=sampled(p,args.samples,args.seed);rows.append(r);print(json.dumps(r),flush=True)
        out.write_text(json.dumps({'model':'unbounded RNE; experimental checker, not Lean','rows':rows,
                                   'elapsed_seconds':time.time()-started},indent=2))
