import Selector.Checker

namespace CoefficientSelector
open ExactFDiv

theorem kernel_scale (p : ℕ) (h l x : ℚ) {s : ℚ} (hs : s = 1 ∨ s = -1) (i j : ℤ) :
    kernel p (h*2^j) (l*2^j) (s*x*2^i) = s * kernel p h l x * 2^(i+j) := by
  have hpow := zpow_split i j
  have hlo : s*x*2^i*(l*2^j) = s*(x*l)*2^(i+j) := by rw [hpow]; ring
  unfold kernel
  rw [hlo, rneU_smul p hs]
  have hsum : s*x*2^i*(h*2^j) + s*rneU p (x*l)*2^(i+j) =
      s*(x*h+rneU p (x*l))*2^(i+j) := by rw [hpow]; ring
  rw [hsum, rneU_smul p hs]

/-- The accepted normalized pair lifts to arbitrary dividend signs and binary scales.
Here the divisor is positive; changing its sign negates both supplied coefficients. -/
theorem check_sound_scaled {p : ℕ} {Y : ℤ} {c₁ c₂ : GridCert} {c : Coeff}
    (hc : check p Y c₁ c₂ c = true) {X : ℤ}
    (hX1 : (2:ℤ)^p ≤ 2*X) (hX2 : X < (2:ℤ)^p)
    {s : ℚ} (hs : s = 1 ∨ s = -1) (i j : ℤ) :
    kernel p (c.h*2^(-j)) (c.l*2^(-j)) (s*X*2^i) =
      rneU p ((s*X*2^i)/((Y:ℚ)*2^j)) := by
  rw [kernel_scale p c.h c.l (X:ℚ) hs i (-j), check_sound hc hX1 hX2]
  have heq : (s*(X:ℚ)*2^i)/((Y:ℚ)*2^j) = s*((X:ℚ)/Y)*2^(i+ -j) := by
    rw [zpow_split, zpow_neg]; ring
  rw [heq, rneU_smul p hs]

end CoefficientSelector
