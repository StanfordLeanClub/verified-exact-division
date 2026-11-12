import Selector.Stability
import Selector.Candidates

namespace CoefficientSelector
open ExactFDiv
local instance : LinearOrder ℤ := Int.instLinearOrder

structure Coeff where
  h : ℚ
  l : ℚ
  e : ℤ
  deriving DecidableEq, Repr

/-- An executable, exact-rational acceptance test. Inverse witnesses and candidate
coefficients are untrusted inputs. All its premises are checked, including representability. -/
def check (p : ℕ) (Y : ℤ) (c₁ c₂ : GridCert) (c : Coeff) : Bool :=
  let P : ℤ := 2^p
  let E := errorBound p Y c.h c.l c.e
  decide (2 ≤ p ∧ P ≤ 2*Y ∧ Y < P ∧ c₁.Valid P Y ∧ c₂.Valid (2*P) Y ∧
    rneU p c.h = c.h ∧ rneU p c.l = c.l ∧
    ((2:ℚ)^p-1)*|c.l| ≤ (2:ℚ)^p*(2:ℚ)^c.e ∧ E < 1/(2*(2:ℚ)^p) ∧
    (candidates P P Y E c₁ ∪ candidates P (2*P) Y E c₂).filter
      (fun (X : ℤ) => kernel p c.h c.l X ≠ rneU p ((X:ℚ)/Y)) = ∅)

/-- Passing the checker proves correctness for EVERY normalized significand,
not just for the inputs evaluated by the checker. -/
theorem check_sound {p : ℕ} {Y : ℤ} {c₁ c₂ : GridCert} {c : Coeff}
    (hcheck : check p Y c₁ c₂ c = true) {X : ℤ}
    (hX1 : (2:ℤ)^p ≤ 2*X) (hX2 : X < (2:ℤ)^p) :
    kernel p c.h c.l X = rneU p ((X:ℚ)/Y) := by
  unfold check at hcheck
  have hc := of_decide_eq_true hcheck
  rcases hc with ⟨hp, hY1, hY2, hg1, hg2, _, _, hl, hE, hok⟩
  have hP0 : (0:ℤ) < 2^p := by positivity
  have hx0 : 0 ≤ X := by omega
  have hy0 : 0 < Y := by omega
  by_cases hmem : X ∈ candidates (2^p) (2^p) Y (errorBound p Y c.h c.l c.e) c₁ ∪
      candidates (2^p) (2*2^p) Y (errorBound p Y c.h c.l c.e) c₂
  · by_contra hn
    exact Finset.filter_eq_empty_iff.mp hok hmem hn
  · apply normalized_stable hp hX1 hX2 hY1 hY2 hE (error_bound (by omega) hx0 hX2 hl)
    · intro k
      by_contra hn
      have hn' : |(X:ℚ)/Y-(2*k+1)/(2:ℚ)^p| ≤ errorBound p Y c.h c.l c.e := by linarith
      apply hmem
      apply Finset.mem_union_left
      apply candidates_complete hg1 hP0 hy0 hx0 hX1 hX2
      simpa only [Int.cast_pow, Int.cast_ofNat] using hn'
    · intro k
      by_contra hn
      have hn' : |(X:ℚ)/Y-(2*k+1)/(2*(2:ℚ)^p)| ≤ errorBound p Y c.h c.l c.e := by linarith
      apply hmem
      apply Finset.mem_union_right
      apply candidates_complete hg2 (by positivity) hy0 hx0 hX1 hX2
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hn'

theorem check_float {p : ℕ} {Y : ℤ} {c₁ c₂ : GridCert} {c : Coeff}
    (hc : check p Y c₁ c₂ c = true) : IsFloat p c.h ∧ IsFloat p c.l := by
  unfold check at hc
  rcases of_decide_eq_true hc with ⟨hp, _, _, _, _, hh, hl, _⟩
  constructor
  · rw [← hh]; exact (rneU_nearest (by omega) _).1
  · rw [← hl]; exact (rneU_nearest (by omega) _).1

/-- The search order is a policy input: same-sign pairs may be placed first.
Failure returns none, leaving hardware division as the consumer's fallback. -/
def select (p : ℕ) (Y : ℤ) (c₁ c₂ : GridCert) : List Coeff → Option Coeff
  | [] => none
  | c :: cs => if check p Y c₁ c₂ c then some c else select p Y c₁ c₂ cs

theorem select_checked {p : ℕ} {Y : ℤ} {c₁ c₂ : GridCert} {cs : List Coeff} {c : Coeff}
    (hs : select p Y c₁ c₂ cs = some c) : check p Y c₁ c₂ c = true := by
  induction cs with
  | nil => simp [select] at hs
  | cons a cs ih =>
    simp only [select] at hs
    split at hs
    · rename_i ha
      have he : a = c := Option.some.inj hs
      simpa [he] using ha
    · exact ih hs

theorem select_sound {p : ℕ} {Y : ℤ} {c₁ c₂ : GridCert} {cs : List Coeff} {c : Coeff}
    (hs : select p Y c₁ c₂ cs = some c) {X : ℤ}
    (hX1 : (2:ℤ)^p ≤ 2*X) (hX2 : X < (2:ℤ)^p) :
    kernel p c.h c.l X = rneU p ((X:ℚ)/Y) :=
  check_sound (select_checked hs) hX1 hX2

end CoefficientSelector
