import ExactFDiv.Checker

namespace CoefficientSelector
local instance : LinearOrder ℤ := Int.instLinearOrder
local instance : DecidableEq ℤ := Int.decEq
local instance : DecidableLE ℤ := Int.decLe
local instance : DecidableLT ℤ := Int.decLt
attribute [-instance] Int.instConditionallyCompleteLinearOrder

/-- Untrusted integer witnesses: checked equations replace trust in an inverse routine. -/
structure GridCert where
  g : ℤ
  a : ℤ
  m : ℤ
  u : ℤ
  v : ℤ
  deriving DecidableEq, Repr

def GridCert.Valid (c : GridCert) (A Y : ℤ) : Prop :=
  0 < c.g ∧ 0 < c.m ∧ A = c.g*c.a ∧ Y = c.g*c.m ∧
  c.u*c.a + c.v*c.m = 1 ∧ c.a % 2 = 0 ∧ c.m % 2 = 1

instance (c : GridCert) (A Y : ℤ) : Decidable (c.Valid A Y) := by
  unfold GridCert.Valid; infer_instance

/-- The parity filter must precede progression enumeration: zero residuals can otherwise
produce enormous lists for even divisors, although no odd midpoint can be reached. -/
def progression (P : ℤ) (c : GridCert) (n : ℤ) : Finset ℤ :=
  if n % c.g = 0 ∧ (n/c.g) % 2 = 1 then
    (((Finset.Icc 0 ((P-1)/c.m)).image
      (fun t => (c.u*(n/c.g)) % c.m + c.m*t)).filter (fun X => P ≤ 2*X ∧ X < P))
  else ∅

def candidates (P A Y : ℤ) (E : ℚ) (c : GridCert) : Finset ℤ :=
  (Finset.Icc (-⌊E*A*Y⌋) ⌊E*A*Y⌋).biUnion (progression P c)

theorem progression_complete {P A Y X k n : ℤ} {c : GridCert}
    (hc : c.Valid A Y) (hx0 : 0 ≤ X) (hx1 : P ≤ 2*X) (hx2 : X < P)
    (hn : A*X - (2*k+1)*Y = n) : X ∈ progression P c n := by
  rcases hc with ⟨hg, hm, ha, hy, hu, hpa, hpm⟩
  have heq : n = c.g*(c.a*X-(2*k+1)*c.m) := by rw [← hn, ha, hy]; ring
  have hdiv : n/c.g = c.a*X-(2*k+1)*c.m := by rw [heq, Int.mul_ediv_cancel_left _ (ne_of_gt hg)]
  have hmod : n % c.g = 0 := by rw [heq]; simp
  have hpar : (n/c.g)%2 = 1 := by
    rw [hdiv]
    have haeven : (c.a*X)%2 = 0 := by rw [Int.mul_emod, hpa]; norm_num
    have hmodd : ((2*k+1)*c.m)%2 = 1 := by rw [Int.mul_emod, hpm]; omega
    rw [Int.sub_emod, haeven, hmodd]; norm_num
  have hres : X % c.m = (c.u*(n/c.g)) % c.m := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(c.u*(2*k+1)+c.v*X), ?_⟩
    rw [hdiv]
    linear_combination X*hu
  have hdecomp : (c.u*(n/c.g)) % c.m + c.m*(X/c.m) = X := by
    rw [← hres]; exact Int.emod_add_mul_ediv X c.m
  have ht0 : 0 ≤ X/c.m := Int.ediv_nonneg hx0 hm.le
  have ht1 : X/c.m ≤ (P-1)/c.m := Int.ediv_le_ediv hm (by omega)
  unfold progression
  rw [if_pos ⟨hmod, hpar⟩]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨X/c.m, Finset.mem_Icc.mpr ⟨ht0, ht1⟩, hdecomp⟩, hx1, hx2⟩

/-- Every input close enough to an odd midpoint is enumerated by the small residual search. -/
theorem candidates_complete {P A Y X k : ℤ} {E : ℚ} {c : GridCert}
    (hc : c.Valid A Y) (ha0 : 0 < A) (hy0 : 0 < Y)
    (hx0 : 0 ≤ X) (hx1 : P ≤ 2*X) (hx2 : X < P)
    (hnear : |(X:ℚ)/Y - (2*k+1)/A| ≤ E) : X ∈ candidates P A Y E c := by
  let n := A*X-(2*k+1)*Y
  have haq : (0:ℚ) < A := by exact_mod_cast ha0
  have hyq : (0:ℚ) < Y := by exact_mod_cast hy0
  have hnq : (n:ℚ) = ((X:ℚ)/Y - (2*k+1)/A) * ((A:ℚ)*Y) := by
    dsimp [n]; push_cast; field_simp
  have hnabs : (|n|:ℚ) ≤ E*A*Y := by
    rw [hnq, abs_mul, abs_of_pos (mul_pos haq hyq)]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hnear (mul_pos haq hyq).le
  have hnN : |n| ≤ ⌊E*A*Y⌋ := Int.le_floor.mpr (by simpa only [Int.cast_abs] using hnabs)
  have hni := abs_le.mp hnN
  apply Finset.mem_biUnion.mpr
  exact ⟨n, Finset.mem_Icc.mpr hni, progression_complete hc hx0 hx1 hx2 rfl⟩

end CoefficientSelector
