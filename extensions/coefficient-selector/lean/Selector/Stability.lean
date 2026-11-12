import ExactFDiv.Checker

/- Arbitrary supplied coefficients. No nearest-reciprocal hypothesis. -/
namespace CoefficientSelector
open ExactFDiv

def kernel (p : ℕ) (h l x : ℚ) : ℚ := rneU p (x * h + rneU p (x * l))

/-- A conservative pre-FMA error bound, with a supplied low-product exponent. -/
def errorBound (p : ℕ) (Y : ℤ) (h l : ℚ) (e : ℤ) : ℚ :=
  ((2:ℚ)^p - 1) * |h + l - 1 / Y| + (2:ℚ)^e / 2

theorem error_bound {p : ℕ} (hp : 1 ≤ p) {X Y : ℤ} {h l : ℚ} {e : ℤ}
    (hx0 : 0 ≤ X) (hx1 : X < (2:ℤ)^p)
    (hl : ((2:ℚ)^p - 1) * |l| ≤ (2:ℚ)^p * (2:ℚ)^e) :
    |(X:ℚ)*h + rneU p ((X:ℚ)*l) - (X:ℚ)/Y| ≤ errorBound p Y h l e := by
  have hxq : (0:ℚ) ≤ X := by exact_mod_cast hx0
  have hxq1 : (X:ℚ) ≤ (2:ℚ)^p - 1 := by exact_mod_cast (show X ≤ (2:ℤ)^p - 1 by omega)
  have ht := (rneU_nearest hp ((X:ℚ)*l)).err hp e (by
    rw [zpow_natCast, abs_mul, abs_of_nonneg hxq]
    exact le_trans (mul_le_mul_of_nonneg_right hxq1 (abs_nonneg _)) hl)
  have hd : |(X:ℚ)*(h+l-1/Y)| ≤ ((2:ℚ)^p-1)*|h+l-1/Y| := by
    rw [abs_mul, abs_of_nonneg hxq]
    exact mul_le_mul_of_nonneg_right hxq1 (abs_nonneg _)
  have heq : (X:ℚ)*h + rneU p ((X:ℚ)*l) - (X:ℚ)/Y =
      (X:ℚ)*(h+l-1/Y) - ((X:ℚ)*l-rneU p ((X:ℚ)*l)) := by ring
  rw [heq]
  exact le_trans (abs_sub _ _) (add_le_add hd ht)

/-- Stability inside a binade when neither adjacent rounding midpoint is close.
The separate lower-edge premise handles the half-sized gap below a power of two. -/
theorem stable_binade {p : ℕ} (hp : 1 ≤ p) {v s E : ℚ} {e : ℤ}
    (hvlo : (2:ℚ)^((p:ℤ)-1) * 2^e ≤ v)
    (hvhi : v ≤ (2:ℚ)^(p:ℤ) * 2^e)
    (hv0 : 0 ≤ v)
    (herr : |s-v| ≤ E)
    (hedge : (2:ℚ)^((p:ℤ)-1) * 2^e - 2^e/4 < s)
    (hsep : ∀ k : ℤ, E < |v - (2*k+1)*(2:ℚ)^e/2|) :
    rneU p s = rneU p v := by
  let q := rneU p v
  have hq : IsNearest p v q := rneU_nearest hp v
  have hloF : IsFloat p ((2:ℚ)^((p:ℤ)-1) * 2^e) := by
    rw [← zpow_split]
    exact ⟨1, (p:ℤ)-1+e, one_lt_two_pow hp, by simp⟩
  have hhiF : IsFloat p ((2:ℚ)^(p:ℤ) * 2^e) := by
    rw [← zpow_split]
    exact ⟨1, (p:ℤ)+e, one_lt_two_pow hp, by simp⟩
  have hqlo := hq.ge_of_ge hloF hvlo
  have hqhi := hq.le_of_le hhiF hvhi
  obtain ⟨k, hk⟩ := float_grid hq.1 e hqlo
  have hd := two_zpow_pos e
  have hklo : (2:ℚ)^((p:ℤ)-1) ≤ k := by rw [hk] at hqlo; nlinarith
  have hkhi : (k:ℚ) ≤ (2:ℚ)^(p:ℤ) := by rw [hk] at hqhi; nlinarith
  have hqe := hq.err hp e (by rw [abs_of_nonneg hv0]; exact hvhi)
  rw [hk, abs_le] at hqe
  have hplus := hsep k
  have hminus := hsep (k-1)
  have hab1 : v - (2*(k:ℚ)+1)*2^e/2 ≤ 0 := by linarith [hqe.2]
  have hab2 : 0 ≤ v - (2*((k:ℚ)-1)+1)*2^e/2 := by linarith [hqe.1]
  rw [abs_of_nonpos hab1] at hplus
  push_cast at hminus
  rw [abs_of_nonneg hab2] at hminus
  have hs := abs_le.mp herr
  have hclose : |s - (k:ℚ)*2^e| < (2:ℚ)^e/2 := by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]
  have hres := nearest_unique hp (rneU_nearest hp s) k e hklo hkhi hclose (by
    intro heq; rw [heq]; linarith)
  exact hres.trans hk.symm

/-- Normalized quotient stability away from both binary midpoint grids. -/
theorem normalized_stable {p : ℕ} (hp : 2 ≤ p) {X Y : ℤ} {s E : ℚ}
    (hX1 : (2:ℤ)^p ≤ 2*X) (hX2 : X < (2:ℤ)^p)
    (hY1 : (2:ℤ)^p ≤ 2*Y) (hY2 : Y < (2:ℤ)^p)
    (hE : E < 1/(2*(2:ℚ)^p))
    (herr : |s - (X:ℚ)/Y| ≤ E)
    (hsep1 : ∀ k : ℤ, E < |(X:ℚ)/Y - (2*k+1)/(2:ℚ)^p|)
    (hsep2 : ∀ k : ℤ, E < |(X:ℚ)/Y - (2*k+1)/(2*(2:ℚ)^p)|) :
    rneU p s = rneU p ((X:ℚ)/Y) := by
  have hp1 : 1 ≤ p := by omega
  let P : ℚ := (2:ℚ)^p
  have hP : 0 < P := by dsimp [P]; positivity
  have hx1 : P ≤ 2*(X:ℚ) := by dsimp [P]; exact_mod_cast hX1
  have hx2 : (X:ℚ) ≤ P-1 := by dsimp [P]; exact_mod_cast (show X ≤ (2:ℤ)^p-1 by omega)
  have hy1 : P ≤ 2*(Y:ℚ) := by dsimp [P]; exact_mod_cast hY1
  have hy2 : (Y:ℚ) ≤ P-1 := by dsimp [P]; exact_mod_cast (show Y ≤ (2:ℤ)^p-1 by omega)
  have hy0 : (0:ℚ) < Y := by linarith
  have hv0 : 0 ≤ (X:ℚ)/Y := div_nonneg (by linarith) hy0.le
  have hvhi : (X:ℚ)/Y ≤ 2 := (div_le_iff₀ hy0).mpr (by linarith)
  have hvlo : 1/2 + 1/(2*P) < (X:ℚ)/Y := by
    apply (lt_div_iff₀ hy0).mpr
    have hz : 0 < P-(Y:ℚ) := by linarith
    have hm : (Y:ℚ)/P < 1 := (div_lt_one hP).mpr (by linarith)
    have he : (1/2 + 1/(2*P))*(Y:ℚ) = ((Y:ℚ) + (Y:ℚ)/P)/2 := by ring
    rw [he]; linarith
  have hslo : 1/2 < s := by
    have hh := (abs_le.mp herr).1
    change E < 1/(2*P) at hE
    linarith
  have e0 : (2:ℚ)^(-(p:ℤ)) = 1/P := by
    simp [zpow_neg, P]
  have e1 : (2:ℚ)^(-(p:ℤ)+1) = 2/P := by rw [zpow_succ', e0]; ring
  have ep : (2:ℚ)^(p:ℤ) = P := by simp [P]
  have eh : (2:ℚ)^((p:ℤ)-1) = P/2 := by rw [zpow_pred', ep]
  have hPi : P*(1/P) = 1 := by field_simp
  have hPtwo : P/2*(2/P) = 1 := by field_simp
  have hPtwo' : P*(2/P) = 2 := by field_simp
  by_cases hv1 : 1 ≤ (X:ℚ)/Y
  · apply stable_binade hp1 (e := -(p:ℤ)+1) (E := E)
    · rw [eh, e1, hPtwo]; exact hv1
    · rw [ep, e1, hPtwo']; exact hvhi
    · exact hv0
    · exact herr
    · rw [eh, e1]
      have hh := (abs_le.mp herr).1
      have he : P/2*(2/P) - (2/P)/4 = 1-1/(2*P) := by field_simp; ring
      rw [he]; change E < 1/(2*P) at hE; linarith
    · intro k; rw [e1]; convert hsep1 k using 1 <;> congr 1 <;> ring
  · apply stable_binade hp1 (e := -(p:ℤ)) (E := E)
    · rw [eh, e0]; have he : P/2*(1/P) = 1/2 := by field_simp
      rw [he]; have hz : 0 < 1/(2*P) := by positivity
      linarith
    · rw [ep, e0, hPi]; linarith
    · exact hv0
    · exact herr
    · rw [eh, e0]; have he : P/2*(1/P) = 1/2 := by field_simp
      rw [he]; have hz : 0 < 1/P/4 := by positivity
      linarith
    · intro k; rw [e0]; convert hsep2 k using 1 <;> congr 1 <;> ring

end CoefficientSelector
