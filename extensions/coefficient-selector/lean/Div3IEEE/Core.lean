import Selector.Instances
import ExactFDiv.Algorithm

namespace Div3IEEE
open ExactFDiv

/-- The exact binary32 coefficients and threshold used by selector3.h. -/
def hi : ℚ := 5592405 / 16777216
def lo : ℚ := 11184811 / 562949953421312
def threshold : ℚ := (2:ℚ)^(-100:ℤ)
def round32 : ℚ → IEEE := rneR 24 (-149) 104
def reference (x : IEEE) : IEEE := div round32 x (.num 3)
def raw (x : IEEE) : IEEE := fma round32 x (.num hi) (mul round32 x (.num lo))
def valid32 (x : IEEE) : Prop := Valid 24 (-149) 104 x

theorem hi_pos : 0 < hi := by norm_num [hi]
theorem lo_pos : 0 < lo := by norm_num [lo]
theorem threshold_pos : 0 < threshold := two_zpow_pos _
theorem min_le_threshold : minNormal 24 (-149) < threshold := by norm_num [minNormal, threshold]
theorem low_guard : minNormal 24 (-149) ≤ threshold*lo := by norm_num [minNormal, threshold, lo]
theorem lo_le_one : lo ≤ 1 := by norm_num [lo]
theorem lo_le_third : lo ≤ (1:ℚ)/3 := by norm_num [lo]
theorem three_lo_le_hi : 3*lo ≤ hi := by norm_num [lo,hi]

theorem max_float32 : IsFloatB 24 (-149) (maxFloat 24 104) := by
  refine ⟨16777215,104,by norm_num,by norm_num,?_⟩
  norm_num [maxFloat]

/-- A normal-range low product rounds to a finite nonzero number, and its
bounded rounding equals the unbounded rounding used by the selector proof. -/
theorem round32_normal {z : ℚ} (hlo : minNormal 24 (-149) ≤ |z|)
    (hhi : |z| ≤ maxFloat 24 104) : round32 z = .num (rneU 24 z) := by
  have hn := rne_nearest (p:=24) (by norm_num) (-149) z
  have hl := hn.le_abs (isFloatB_minNormal (by norm_num) (-149)) hlo
  have hh := hn.abs_le max_float32 hhi
  have hz : rne 24 (-149) z ≠ 0 := by
    intro he; rw [he,abs_zero] at hl; exact (minNormal_pos 24 (-149)).not_ge hl
  unfold round32 rneR
  rw [if_neg hz, if_pos hh, rne_eq_rneU hlo]

theorem unbounded {x : ℚ} (hx0 : x ≠ 0) (hxf : IsFloat 24 x) :
    rneU 24 (x*hi + rneU 24 (x*lo)) = rneU 24 (x/3) := by
  obtain ⟨h1,h2,hrep⟩ := sigOf_spec (p:=24) (by norm_num) hx0 hxf
  rcases hrep with h | h
  · rw [h]
    simpa [CoefficientSelector.kernel,hi,lo] using
      CoefficientSelector.div3_scaled_correct (sigOf 24 x) (Int.log 2 |x| - (24:ℤ) + 1) h1 h2 (s:=1) (Or.inl rfl)
  · rw [h]
    simpa [CoefficientSelector.kernel,hi,lo,neg_mul] using
      CoefficientSelector.div3_scaled_correct (sigOf 24 x) (Int.log 2 |x| - (24:ℤ) + 1) h1 h2 (s:=(-1)) (Or.inr rfl)

/-- The new finite-range bridge. No nearest-high-coefficient premise is used. -/
theorem fast_finite_correct {x : ℚ} (hx : ValidNum 24 (-149) 104 x)
    (hg : threshold ≤ |x|) : raw (.num x) = reference (.num x) := by
  have hnpos := minNormal_pos 24 (-149)
  have hp0 : 0 ≤ |x| := abs_nonneg x
  have hlow : minNormal 24 (-149) ≤ |x*lo| := by
    rw [abs_mul, abs_of_pos lo_pos]
    exact low_guard.trans (mul_le_mul_of_nonneg_right hg lo_pos.le)
  have hupp : |x*lo| ≤ maxFloat 24 104 := by
    rw [abs_mul, abs_of_pos lo_pos]
    have h := mul_le_mul_of_nonneg_left lo_le_one hp0
    rw [mul_one] at h
    exact le_trans h hx.2.2
  have hmul := round32_normal hlow hupp
  let t := rneU 24 (x*lo)
  have ht := rneU_nearest (p:=24) (by norm_num) (x*lo)
  have flzero : IsFloat 24 0 := ⟨0,0,by norm_num,by simp⟩
  have ht0 := ht.2 0 flzero
  rw [sub_zero] at ht0
  have htmag : |t| ≤ 2*|x*lo| := by
    have h := abs_sub (x*lo) (x*lo-t)
    rw [sub_sub_cancel] at h
    dsimp [t] at h ⊢
    linarith
  have htri : |x*hi| ≤ |x*hi+t| + |t| := by
    have h := abs_sub (x*hi+t) t
    simpa only [add_sub_cancel_right] using h
  have hlarge : 3*|x*lo| ≤ |x*hi| := by
    rw [abs_mul,abs_mul,abs_of_pos hi_pos,abs_of_pos lo_pos]
    have h := mul_le_mul_of_nonneg_left three_lo_le_hi hp0
    nlinarith
  have hsn : minNormal 24 (-149) ≤ |x*hi+t| := by linarith
  have hs0 : x*hi+t ≠ 0 := by
    intro h; rw [h,abs_zero] at hsn; linarith
  have hqn : minNormal 24 (-149) ≤ |x/3| := by
    have h := mul_le_mul_of_nonneg_left lo_le_third hp0
    rw [abs_mul,abs_of_pos lo_pos] at hlow
    rw [abs_div]; norm_num; linarith
  have hrs : rne 24 (-149) (x*hi+t) ≠ 0 := by
    have h := (rne_nearest (p:=24) (by norm_num) (-149) (x*hi+t)).le_abs
      (isFloatB_minNormal (by norm_num) (-149)) hsn
    intro he; rw [he,abs_zero] at h; linarith
  have hsame : rne 24 (-149) (x*hi+t) = rne 24 (-149) (x/3) := by
    rw [rne_eq_rneU hsn, rne_eq_rneU hqn]
    exact unbounded hx.1 hx.2.1.isFloat
  unfold raw reference
  change fma round32 (.num x) (.num hi) (round32 (x*lo)) = round32 (x/3)
  rw [hmul]
  change (if x*hi+t = 0 then IEEE.zero false else round32 (x*hi+t)) = round32 (x/3)
  rw [if_neg hs0]
  exact rneR_congr hrs hsame

theorem raw_special {x : IEEE} (hx : ∀ v, x ≠ .num v) : raw x = reference x := by
  apply kernel_special round32 hx (by norm_num : (3:ℚ) ≠ 0) hi_pos.ne' lo_pos.ne'
  · norm_num [sgn,hi]
  · norm_num [sgn,hi,lo]

/-- Only finite nonzero values below the threshold need division. -/
def tiny : IEEE → Bool
  | .num v => decide (|v| < threshold)
  | _ => false

/-- Same-sign SIMD lane behavior; specials take the raw multiply/FMA path. -/
def guarded (x : IEEE) : IEEE := if tiny x then reference x else raw x

/-- The scalar tail in efd32_div sends specials to hardware division. -/
def scalar (x : IEEE) : IEEE :=
  match x with
  | .num v => if threshold ≤ |v| then raw x else reference x
  | _ => reference x

theorem guarded_correct (x : IEEE) (hx : valid32 x) : guarded x = reference x := by
  cases x with
  | nan => exact raw_special (x:=.nan) (by intro v h; cases h)
  | zero s => exact raw_special (x:=.zero s) (by intro v h; cases h)
  | inf s => exact raw_special (x:=.inf s) (by intro v h; cases h)
  | num v =>
    unfold guarded tiny
    by_cases hg : |v| < threshold
    · simp [hg]
    · simp only [decide_eq_true_eq, if_neg hg]
      exact fast_finite_correct hx (le_of_not_gt hg)

theorem scalar_correct (x : IEEE) (hx : valid32 x) : scalar x = reference x := by
  cases x with
  | nan => rfl
  | zero s => rfl
  | inf s => rfl
  | num v =>
    dsimp only [scalar]
    split_ifs with h
    · exact fast_finite_correct hx h
    · rfl

theorem subnormal_fallback {x : ℚ} (hx : |x| < minNormal 24 (-149)) :
    tiny (.num x) = true ∧ guarded (.num x) = reference (.num x) := by
  have ht : |x| < threshold := hx.trans min_le_threshold
  simp [tiny,guarded,ht]

theorem signed_zero (s : Bool) : guarded (.zero s) = .zero s := by
  rw [guarded_correct (.zero s) (by trivial)]
  norm_num [reference,div,sgn]

theorem signed_infinity (s : Bool) : guarded (.inf s) = .inf s := by
  rw [guarded_correct (.inf s) (by trivial)]
  norm_num [reference,div,sgn]

theorem nan_correct : guarded .nan = .nan := by rfl

end Div3IEEE
