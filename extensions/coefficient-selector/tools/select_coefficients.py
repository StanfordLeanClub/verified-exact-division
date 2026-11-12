"""Select coefficients for a supplied normalized divisor and emit a Lean certificate.

Use --prove to compile the emitted certificate. Python search results alone are
untrusted. All output is confined to this investigation's directory.
"""
import argparse
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json
import subprocess
import sys

root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'tools'))
import probe_coefficients as probe

ap=argparse.ArgumentParser()
ap.add_argument('--precision',type=int,choices=[24,53],required=True)
ap.add_argument('--significand',type=int,required=True)
ap.add_argument('--prove',action='store_true')
args=ap.parse_args()
p,Y=args.precision,args.significand
P=1<<p
if not P//2<=Y<P: ap.error('significand must be in [2^(precision-1),2^precision)')
h,l=probe.canonical(Y,p)
hd=h if l>=0 else probe.neighbor(h,-1,p)
choices=[('same_sign',hd,probe.rn(F(1,Y)-hd,p)),*probe.variants(Y,p)]
attempts=[]
chosen=None
for name,h,l in choices:
    bad=probe.failures(Y,h,l,p)
    attempts.append(dict(choice=name,failures=bad))
    if not bad:
        chosen=name,h,l
        break
stem=f'Generated_{p}_{Y}'
result=dict(p=p,Y=Y,attempts=attempts,proof_checked=False)
if chosen is None:
    result['status']='fallback_to_division'
else:
    name,h,l=chosen
    e=probe.flog2((P-1)*abs(l))-p+1 if l else -2*p-4
    def grid(A):
        g=gcd(A,Y); a,m=A//g,Y//g
        u=pow(a,-1,m) if m>1 else 0
        return [g,a,m,u,(1-u*a)//m]
    def rat(x): return f'({x.numerator}:ℚ)/{x.denominator}'
    E=(P-1)*abs(h+l-F(1,Y))+probe.pow2(e)/2
    result.update(status='untrusted_candidate',choice=name,h=str(h),l=str(l),e=e,E=str(E))
    lines=['import Selector.Checker', 'namespace CoefficientSelector.'+stem,
           'open ExactFDiv', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000',
           f'def coeff : Coeff := ⟨{rat(h)}, {rat(l)}, {e}⟩',
           'def grid1 : GridCert := ⟨'+', '.join(map(str,grid(P)))+'⟩',
           'def grid2 : GridCert := ⟨'+', '.join(map(str,grid(2*P)))+'⟩',
           f'theorem checked : check {p} {Y} grid1 grid2 coeff = true := by decide +kernel',
           f'theorem correct (X : ℤ) (hlo : (2:ℤ)^{p} ≤ 2*X) (hhi : X < (2:ℤ)^{p}) :',
           f'    kernel {p} coeff.h coeff.l X = rneU {p} ((X:ℚ)/{Y}) := check_sound checked hlo hhi',
           '#print axioms correct', 'end CoefficientSelector.'+stem, '']
    (root/'lean/Selector'/f'{stem}.lean').write_text('\n'.join(lines),encoding='utf-8')
    result['lean_module']=stem
    if args.prove:
        proc=subprocess.run(['lake','env','lean','Selector/'+stem+'.lean'],cwd=root/'lean')
        result['proof_exit_code']=proc.returncode
        result['proof_checked']=proc.returncode==0
        result['status']='certified_unbounded_RNE' if proc.returncode==0 else 'proof_failed'
(root/'results'/f'{stem}.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
if result['status']=='proof_failed': raise SystemExit(1)
