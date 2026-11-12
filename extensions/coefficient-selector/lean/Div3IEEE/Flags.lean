import Div3IEEE.Core

namespace Div3IEEE
open ExactFDiv

/-- Every binary32 coefficient is an integer multiple of the least subnormal.
The upper exponent bound is not needed. -/
theorem coefficient_lattice {x : ℚ} (hx : IsFloatB 24 (-149) x) :
    ∃ n : ℤ, x = n*(2:ℚ)^(-149:ℤ) := by
  obtain ⟨m,e,_,he,rfl⟩ := hx
  let k := (e+149).toNat
  have hk : (k:ℤ) = e+149 := Int.toNat_of_nonneg (by omega)
  refine ⟨m*2^k,?_⟩
  have heq : e = (k:ℤ)+(-149) := by omega
  rw [heq,zpow_split]
  push_cast
  rw [zpow_natCast]
  ring

theorem two_coefficients_ne_third {h l : ℚ}
    (hh : IsFloatB 24 (-149) h) (hl : IsFloatB 24 (-149) l) : 3*(h+l) ≠ 1 := by
  obtain ⟨H,rfl⟩ := coefficient_lattice hh
  obtain ⟨L,rfl⟩ := coefficient_lattice hl
  intro he
  have hq : (3:ℚ)*(H+L) = (2:ℚ)^149 := by
    norm_num at he ⊢
    linarith
  have hz : (3:ℤ)*(H+L) = (2:ℤ)^149 := by exact_mod_cast hq
  norm_num at hz
  omega

/-- Fundamental limit of the two-operation scheme: no finite binary32 pair can
produce 3/3 = 1 with both the low multiply and final FMA exact. Changing the
coefficients cannot by itself repair the inexact-flag mismatch. This is an
arithmetic theorem, not a model of the machine's exception-state register. -/
theorem any_pair_inexact_at_three {h l : ℚ}
    (hh : IsFloatB 24 (-149) h) (hl : IsFloatB 24 (-149) l)
    (hq : rne 24 (-149) (3*h + rne 24 (-149) (3*l)) = 1) :
    rne 24 (-149) (3*l) ≠ 3*l ∨
      rne 24 (-149) (3*h + rne 24 (-149) (3*l)) ≠ 3*h + rne 24 (-149) (3*l) := by
  by_contra hn
  push Not at hn
  obtain ⟨hlx,hfx⟩ := hn
  rw [hlx] at hfx hq
  have he : 3*(h+l) = 1 := by linarith
  exact two_coefficients_ne_third hh hl he

end Div3IEEE
