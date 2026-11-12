"""Emit shared native/Lean boundary fixtures; Lean proves each expected value."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
cases=[
 ('positive_zero',0x00000000,0x00000000),('negative_zero',0x80000000,0x80000000),
 ('min_subnormal',0x00000001,0x00000000),('negative_min_subnormal',0x80000001,0x80000000),
 ('two_subnormal_quanta',0x00000002,0x00000001),('negative_two_quanta',0x80000002,0x80000001),
 ('three_subnormal_quanta',0x00000003,0x00000001),
 ('max_subnormal',0x007fffff,0x002aaaaa),('min_normal',0x00800000,0x002aaaab),
 ('negative_min_normal',0x80800000,0x802aaaab),('first_normal_quotient',0x01400000,0x00800000),
 ('below_guard',0x0d7fffff,0x0caaaaaa),('at_guard',0x0d800000,0x0caaaaab),
 ('above_guard',0x0d800001,0x0caaaaac),('three',0x40400000,0x3f800000),
 ('max_finite',0x7f7fffff,0x7eaaaaaa),('negative_max_finite',0xff7fffff,0xfeaaaaaa),
 ('positive_infinity',0x7f800000,0x7f800000),('negative_infinity',0xff800000,0xff800000),
 ('quiet_nan',0x7fc12345,0x7fc00000),('negative_quiet_nan',0xffc12345,0x7fc00000),
 ('signaling_nan',0x7f812345,0x7fc00000),('negative_signaling_nan',0xff812345,0x7fc00000)]
lines=['import Div3IEEE.Array','namespace Div3IEEE','open ExactFDiv',
       'set_option maxRecDepth 100000','set_option maxHeartbeats 4000000','']
for name,x,q in cases:
    lines += [f'theorem case_{name} : nativeGuarded (BitVec.ofNat 32 {x}) = decode (BitVec.ofNat 32 {q}) := by',
              '  rw [nativeGuarded_correct]', '  decide +kernel','']
lines += [
 'theorem unguarded_min_normal_wrong :',
 '    raw (decode (BitVec.ofNat 32 0x00800000)) = decode (BitVec.ofNat 32 0x002aaaaa) := by decide +kernel',
 'theorem unguarded_fails :',
 '    raw (decode (BitVec.ofNat 32 0x00800000)) ≠ reference (decode (BitVec.ofNat 32 0x00800000)) := by decide +kernel',
 '',
 '/-- The low multiply at x=3 is inexact although the reference quotient is exact.',
 'This is why equality of sticky exception flags is not a valid extension of the value claim. -/',
 'theorem three_low_product_inexact : rne 24 (-149) (3*lo) ≠ 3*lo := by decide +kernel',
 'theorem three_reference_exact : rne 24 (-149) ((3:ℚ)/3) = 1 := by decide +kernel',
 '', 'end Div3IEEE','']
(root/'lean/Div3IEEE/Cases.lean').write_text('\n'.join(lines),encoding='utf-8')
native=['typedef struct { const char *name; uint32_t input,expected; } fixture;',
        'static const fixture fixtures[] = {']
native += [f'    {{"{name}",0x{x:08x}u,0x{q:08x}u}},' for name,x,q in cases]
native += ['};','']
(root/'native').mkdir(exist_ok=True)
(root/'native/case_words.h').write_text('\n'.join(native))
(root/'results/cases.json').write_text(json.dumps([dict(name=n,input=f'{x:08x}',expected=f'{q:08x}') for n,x,q in cases],indent=2))
print('Generated',len(cases),'shared native/Lean fixtures')
