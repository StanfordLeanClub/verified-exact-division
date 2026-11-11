/-
Exact division by an invariant floating-point divisor — main theorem (unbounded exponent).

`alg2_core`: for integer significands `2^(p-1) ≤ X, Y < 2^p` (`p ≥ 2`), with
  zh a nearest float of 1/Y,  zl a nearest float of 1/Y - zh,
  t1 a nearest float of X*zl, q2 a nearest float of X*zh + t1,
`q2` equals every nearest float `q` of `X / Y`, provided `Y ≤ X`, or there is no integer `B`
with `X * 2^(p+1) - B * Y = ±1`.

This is the correctness of "Algorithm 2" of Brisebarre, Muller and Raina (IEEE TC 2004) together
with the characterisation of its only possible failures; no tie-breaking rule is assumed.

Notation in the proofs: `P = 2^p`, `a = 1/P`, `x = X`, `y = Y`, `b = 1/y`.
-/
import ExactFDiv.Basic

namespace ExactFDiv

/-- `X * 2^n = odd * Y` is impossible for `0 < Y < 2^n`. -/
theorem odd_mul_ne_pow {n : ℕ} {X Y m : ℤ} (hY0 : 0 < Y) (hY : Y < 2 ^ n)
    (h : X * 2 ^ n = (2 * m + 1) * Y) : False := by
  have h2 : IsCoprime (2:ℤ) (2 * m + 1) := ⟨-m, 1, by ring⟩
  have h3 : IsCoprime ((2:ℤ) ^ n) (2 * m + 1) := h2.pow_left
  have h4 : (2:ℤ) ^ n ∣ Y * (2 * m + 1) := ⟨X, by rw [mul_comm Y, ← h]; ring⟩
  have h5 : (2:ℤ) ^ n ∣ Y := h3.dvd_of_dvd_mul_right h4
  have h6 := Int.le_of_dvd hY0 h5
  linarith

theorem one_lt_two_pow {p : ℕ} (hp : 1 ≤ p) : |(1:ℤ)| < 2 ^ p := by
  rw [abs_one]
  exact one_lt_pow₀ (by norm_num) (by omega)

theorem pw1 (p : ℕ) : (2:ℚ) ^ (-(p:ℤ)) = ((2:ℚ) ^ (p:ℤ))⁻¹ := zpow_neg _ _

theorem pw2 (p : ℕ) : (2:ℚ) ^ ((p:ℤ) * (-2)) = (((2:ℚ) ^ (p:ℤ))⁻¹) ^ 2 := by
  rw [zpow_mul, zpow_neg, zpow_ofNat, inv_pow]

theorem pw3 (p : ℕ) : (2:ℚ) ^ ((p:ℤ) * (-3)) = (((2:ℚ) ^ (p:ℤ))⁻¹) ^ 3 := by
  rw [zpow_mul, zpow_neg, zpow_ofNat, inv_pow]

/-- Step 1: the value `s = x*zh + t1` actually rounded by the last operation is within
`a^2 = 2^(-2p)` of the exact quotient `x*b = x/y`. -/
theorem err_bound {p : ℕ} (hp1 : 1 ≤ p) {P a b x zh zl t1 : ℚ}
    (hP : P = 2 ^ (p:ℤ)) (haP : a * P = 1) (hPpos : 0 < P)
    (hbpos : 0 < b) (hb2a : b ≤ 2 * a) (hxpos : 0 < x) (hx2 : x < P)
    (hzh : IsNearest p b zh) (hzl : IsNearest p (b - zh) zl) (ht1 : IsNearest p (x * zl) t1) :
    |x * zh + t1 - x * b| < a * a := by
  have ha : a = P⁻¹ := eq_inv_of_mul_eq_one_left haP
  have hapos : 0 < a := by rw [ha]; exact inv_pos.mpr hPpos
  have haa : 0 < a * a := mul_pos hapos hapos
  have hxa : x * a < 1 := by
    have h1 : a * (P - x) = 1 - x * a := by linear_combination haP
    have h2 : 0 < a * (P - x) := mul_pos hapos (by linarith)
    linarith
  have e2 : (2:ℚ) ^ ((p:ℤ) * (-2)) = a ^ 2 := by rw [pw2, ← hP, ← ha]
  have e3 : (2:ℚ) ^ ((p:ℤ) * (-3)) = a ^ 3 := by rw [pw3, ← hP, ← ha]
  have e2' : (2:ℚ) ^ ((p:ℤ) * (-2) + 1) = 2 * a ^ 2 := by rw [zpow_succ', e2]; ring
  have fl_a2 : IsFloat p (a ^ 2) := ⟨1, (p:ℤ) * (-2), one_lt_two_pow hp1, by rw [e2]; simp⟩
  have hzh' : |b - zh| ≤ a ^ 2 := by
    have h := hzh.err hp1 ((p:ℤ) * (-2) + 1) (by
      rw [← hP, e2', abs_of_pos hbpos]
      have : P * (2 * a ^ 2) = 2 * a := by linear_combination (2 * a) * haP
      linarith)
    rw [e2'] at h; linarith
  have hzl' : |b - zh - zl| ≤ a ^ 3 / 2 := by
    have h := hzl.err hp1 ((p:ℤ) * (-3)) (by
      rw [← hP, e3]
      have : P * a ^ 3 = a ^ 2 := by linear_combination (a ^ 2) * haP
      linarith)
    rw [e3] at h; exact h
  have hzl_abs : |zl| ≤ a ^ 2 := by
    have h := abs_le.mp hzh'
    exact abs_le.mpr ⟨hzl.ge_of_ge fl_a2.neg h.1, hzl.le_of_le fl_a2 h.2⟩
  have ht1' : |x * zl - t1| ≤ a ^ 2 / 2 := by
    have h := ht1.err hp1 ((p:ℤ) * (-2)) (by
      rw [← hP, e2, abs_mul, abs_of_pos hxpos]
      exact mul_le_mul hx2.le hzl_abs (abs_nonneg _) hPpos.le)
    rw [e2] at h; exact h
  have e : x * zh + t1 - x * b = -(x * (b - zh - zl)) - (x * zl - t1) := by ring
  have h1 : |x * (b - zh - zl)| ≤ x * (a ^ 3 / 2) := by
    rw [abs_mul, abs_of_pos hxpos]; exact mul_le_mul_of_nonneg_left hzl' hxpos.le
  have h2 : x * (a ^ 3 / 2) < a ^ 2 / 2 := by
    have h3 : 0 < a * a * (1 - x * a) := mul_pos haa (by linarith)
    have h4 : a * a * (1 - x * a) = a ^ 2 - 2 * (x * (a ^ 3 / 2)) := by ring
    linarith
  have ha2 : a * a = a ^ 2 := by ring
  rw [e, ha2]
  calc |-(x * (b - zh - zl)) - (x * zl - t1)|
      ≤ |-(x * (b - zh - zl))| + |x * zl - t1| := abs_sub _ _
    _ = |x * (b - zh - zl)| + |x * zl - t1| := by rw [abs_neg]
    _ < a ^ 2 := by linarith

/-- Step 2, case `Y ≤ X` (quotient in `[1, 2)`): no rounding breakpoint lies within `a^2` of
`X / Y`, so `s` and `X / Y` have the same nearest float. -/
theorem finish_ge {p : ℕ} (hp : 2 ≤ p) (X Y : ℤ) (hY0 : 0 < Y) (hY2 : Y < 2 ^ p)
    {P a b x y s q2 q : ℚ}
    (hP : P = 2 ^ (p:ℤ)) (hx : x = (X:ℚ)) (hy : y = (Y:ℚ))
    (haP : a * P = 1) (hby : b * y = 1) (hP4 : 4 ≤ P)
    (hx2 : x < P) (hy2 : y < P) (hy1 : P ≤ 2 * y) (hyx : y ≤ x)
    (herr : |s - x * b| < a * a)
    (hq2 : IsNearest p s q2) (hq : IsNearest p (x * b) q) : q2 = q := by
  have hp1 : 1 ≤ p := by omega
  have hPpos : (0:ℚ) < P := by linarith
  have hypos : 0 < y := by linarith
  have hxpos : 0 < x := by linarith
  have ha : a = P⁻¹ := eq_inv_of_mul_eq_one_left haP
  have hb : b = y⁻¹ := eq_inv_of_mul_eq_one_left hby
  have hapos : 0 < a := by rw [ha]; exact inv_pos.mpr hPpos
  have hbpos : 0 < b := by rw [hb]; exact inv_pos.mpr hypos
  have habpos : 0 < a * b := mul_pos hapos hbpos
  have hab : a < b := by
    have h1 : b - a = a * b * (P - y) := by linear_combination a * hby - b * haP
    have h2 : 0 < a * b * (P - y) := mul_pos habpos (by linarith)
    linarith
  have hb2a : b ≤ 2 * a := by
    have h1 : 2 * a - b = a * b * (2 * y - P) := by linear_combination b * haP - 2 * a * hby
    have h2 : 0 ≤ a * b * (2 * y - P) := mul_nonneg habpos.le (by linarith)
    linarith
  have ha4 : 4 * a ≤ 1 := by
    have h1 : a * (P - 4) = 1 - 4 * a := by linear_combination haP
    have h2 : 0 ≤ a * (P - 4) := mul_nonneg hapos.le (by linarith)
    linarith
  have hxa : x * a < 1 := by
    have h1 : a * (P - x) = 1 - x * a := by linear_combination haP
    have h2 : 0 < a * (P - x) := mul_pos hapos (by linarith)
    linarith
  have hab' : a * a < a * b := mul_lt_mul_of_pos_left hab hapos
  have haa4 : a * a ≤ a / 4 := by
    have h1 : 0 ≤ a * (1 - 4 * a) := mul_nonneg hapos.le (by linarith)
    have h2 : a * (1 - 4 * a) = a - 4 * (a * a) := by ring
    linarith
  have hPc : ((2 ^ p : ℤ) : ℚ) = P := by rw [hP]; exact cast_two_pow p
  have e1 : (2:ℚ) ^ (-(p:ℤ)) = a := by rw [pw1, ← hP, ← ha]
  have e1' : (2:ℚ) ^ (-(p:ℤ) + 1) = 2 * a := by rw [zpow_succ', e1]; ring
  have eH : (2:ℚ) ^ ((p:ℤ) - 1) = P / 2 := by rw [zpow_pred', hP]
  have fl_one : IsFloat p 1 := ⟨1, 0, one_lt_two_pow hp1, by simp⟩
  have fl_two : IsFloat p 2 := ⟨1, 1, one_lt_two_pow hp1, by norm_num⟩
  have herr' := abs_lt.mp herr
  have htpos : 0 < x * b := mul_pos hxpos hbpos
  have hyP : 0 < y * P := mul_pos hypos hPpos
  have ht1le : 1 ≤ x * b := by
    have h1 : b * (x - y) = x * b - 1 := by linear_combination -hby
    have h2 : 0 ≤ b * (x - y) := mul_nonneg hbpos.le (by linarith)
    linarith
  have ht2 : x * b ≤ 2 := by
    have h1 : 0 ≤ x * (2 * a - b) := mul_nonneg hxpos.le (by linarith)
    have h2 : x * (2 * a - b) = 2 * (x * a) - x * b := by ring
    linarith
  have hq1 : 1 ≤ q := hq.ge_of_ge fl_one ht1le
  have hq2' : q ≤ 2 := hq.le_of_le fl_two ht2
  have hPa : P / 2 * (2 * a) = 1 := by linear_combination haP
  obtain ⟨k, hk⟩ := float_grid hq.1 (-(p:ℤ) + 1) (by rw [eH, e1']; linarith)
  rw [e1'] at hk
  have hkP1 : P / 2 ≤ k := by
    rw [hk] at hq1
    have h1 : P * ((k:ℚ) * (2 * a) - 1) = 2 * k - P := by linear_combination (2 * (k:ℚ)) * haP
    have h2 : 0 ≤ P * ((k:ℚ) * (2 * a) - 1) := mul_nonneg hPpos.le (by linarith)
    linarith
  have hkP2 : (k:ℚ) ≤ P := by
    rw [hk] at hq2'
    have h1 : P * (2 - (k:ℚ) * (2 * a)) = 2 * P - 2 * k := by
      linear_combination (-2 * (k:ℚ)) * haP
    have h2 : 0 ≤ P * (2 - (k:ℚ) * (2 * a)) := mul_nonneg hPpos.le (by linarith)
    linarith
  have hqe := hq.err hp1 (-(p:ℤ) + 1) (by
    rw [← hP, e1', abs_of_pos htpos]
    have : P * (2 * a) = 2 := by linear_combination 2 * haP
    linarith)
  rw [e1', hk] at hqe
  have hqe' := abs_le.mp hqe
  -- the two neighbouring breakpoints, as integers
  obtain ⟨N1, hN1d⟩ : ∃ N : ℤ, N = X * 2 ^ p - (2 * k + 1) * Y := ⟨_, rfl⟩
  obtain ⟨N2, hN2d⟩ : ∃ N : ℤ, N = X * 2 ^ p - (2 * (k - 1) + 1) * Y := ⟨_, rfl⟩
  have cN1 : (N1:ℚ) = x * P - (2 * k + 1) * y := by
    rw [hN1d, hx, hy, ← hPc]; push_cast; ring
  have cN2 : (N2:ℚ) = x * P - (2 * k - 1) * y := by
    rw [hN2d, hx, hy, ← hPc]; push_cast; ring
  have i1 : (x * b - k * (2 * a) - a) * (y * P) = x * P - (2 * k + 1) * y := by
    linear_combination (x * P) * hby - ((2 * k + 1) * y) * haP
  have i2 : (x * b - k * (2 * a) + a) * (y * P) = x * P - (2 * k - 1) * y := by
    linear_combination (x * P) * hby - ((2 * k - 1) * y) * haP
  have habyP : (a * b) * (y * P) = 1 := by linear_combination (a * P) * hby + haP
  have hN1 : N1 ≤ -1 := by
    have h1 : (N1:ℚ) ≤ 0 := by
      rw [cN1, ← i1]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hqe'.2]) hyP.le
    have h2 : N1 ≤ 0 := by exact_mod_cast h1
    have h3 : N1 ≠ 0 := fun h0 =>
      odd_mul_ne_pow (X := X) hY0 hY2 (m := k) (by rw [hN1d] at h0; linear_combination h0)
    omega
  have hN2 : 1 ≤ N2 := by
    have h1 : (0:ℚ) ≤ (N2:ℚ) := by
      rw [cN2, ← i2]; exact mul_nonneg (by linarith [hqe'.1]) hyP.le
    have h2 : 0 ≤ N2 := by exact_mod_cast h1
    have h3 : N2 ≠ 0 := fun h0 =>
      odd_mul_ne_pow (X := X) hY0 hY2 (m := k - 1) (by rw [hN2d] at h0; linear_combination h0)
    omega
  have hN1q : x * P - (2 * k + 1) * y ≤ -1 := by rw [← cN1]; exact_mod_cast hN1
  have hN2q : 1 ≤ x * P - (2 * k - 1) * y := by rw [← cN2]; exact_mod_cast hN2
  have j1 : x * b - k * (2 * a) - a = (x * P - (2 * k + 1) * y) * (a * b) := by
    rw [← i1]; linear_combination (-(x * b - k * (2 * a) - a)) * habyP
  have j2 : x * b - k * (2 * a) + a = (x * P - (2 * k - 1) * y) * (a * b) := by
    rw [← i2]; linear_combination (-(x * b - k * (2 * a) + a)) * habyP
  have u1 : x * b - k * (2 * a) - a ≤ -(a * b) := by
    rw [j1]
    have := mul_le_mul_of_nonneg_right hN1q habpos.le
    linarith
  have u2 : a * b ≤ x * b - k * (2 * a) + a := by
    rw [j2]
    have := mul_le_mul_of_nonneg_right hN2q habpos.le
    linarith
  have hfin := nearest_unique hp1 hq2 k (-(p:ℤ) + 1) (by rw [eH]; exact hkP1)
    (by rw [← hP]; exact hkP2)
    (by rw [e1', abs_lt]; constructor <;> linarith [herr'.1, herr'.2])
    (by
      intro hkeq
      rw [eH] at hkeq
      rw [e1', hkeq, hPa]
      linarith [herr'.1])
  rw [e1'] at hfin
  rw [hfin, hk]

/-- Step 2, case `X < Y` (quotient in `(1/2, 1)`): the same, provided `X * 2^(p+1) - B * Y`
is never `±1`. -/
theorem finish_lt {p : ℕ} (hp : 2 ≤ p) (X Y : ℤ) (hY0 : 0 < Y) (hY2 : Y < 2 ^ p)
    (hno : ∀ B : ℤ, X * 2 ^ (p + 1) - B * Y ≠ 1 ∧ X * 2 ^ (p + 1) - B * Y ≠ -1)
    {P a b x y s q2 q : ℚ}
    (hP : P = 2 ^ (p:ℤ)) (hx : x = (X:ℚ)) (hy : y = (Y:ℚ))
    (haP : a * P = 1) (hby : b * y = 1) (hP4 : 4 ≤ P)
    (hx1 : P ≤ 2 * x) (hy2 : y < P) (hxy : x < y)
    (herr : |s - x * b| < a * a)
    (hq2 : IsNearest p s q2) (hq : IsNearest p (x * b) q) : q2 = q := by
  have hp1 : 1 ≤ p := by omega
  have hPpos : (0:ℚ) < P := by linarith
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have ha : a = P⁻¹ := eq_inv_of_mul_eq_one_left haP
  have hb : b = y⁻¹ := eq_inv_of_mul_eq_one_left hby
  have hapos : 0 < a := by rw [ha]; exact inv_pos.mpr hPpos
  have hbpos : 0 < b := by rw [hb]; exact inv_pos.mpr hypos
  have habpos : 0 < a * b := mul_pos hapos hbpos
  have hab : a < b := by
    have h1 : b - a = a * b * (P - y) := by linear_combination a * hby - b * haP
    have h2 : 0 < a * b * (P - y) := mul_pos habpos (by linarith)
    linarith
  have ha4 : 4 * a ≤ 1 := by
    have h1 : a * (P - 4) = 1 - 4 * a := by linear_combination haP
    have h2 : 0 ≤ a * (P - 4) := mul_nonneg hapos.le (by linarith)
    linarith
  have hxa2 : 1 ≤ 2 * (x * a) := by
    have h1 : a * (2 * x - P) = 2 * (x * a) - 1 := by linear_combination -haP
    have h2 : 0 ≤ a * (2 * x - P) := mul_nonneg hapos.le (by linarith)
    linarith
  have hab' : a * a < a * b := mul_lt_mul_of_pos_left hab hapos
  have haa4 : a * a ≤ a / 4 := by
    have h1 : 0 ≤ a * (1 - 4 * a) := mul_nonneg hapos.le (by linarith)
    have h2 : a * (1 - 4 * a) = a - 4 * (a * a) := by ring
    linarith
  have hPc : ((2 ^ p : ℤ) : ℚ) = P := by rw [hP]; exact cast_two_pow p
  have e1 : (2:ℚ) ^ (-(p:ℤ)) = a := by rw [pw1, ← hP, ← ha]
  have eH : (2:ℚ) ^ ((p:ℤ) - 1) = P / 2 := by rw [zpow_pred', hP]
  have fl_one : IsFloat p 1 := ⟨1, 0, one_lt_two_pow hp1, by simp⟩
  have fl_half : IsFloat p (1 / 2) := ⟨1, -1, one_lt_two_pow hp1, by norm_num⟩
  have herr' := abs_lt.mp herr
  have htpos : 0 < x * b := mul_pos hxpos hbpos
  have hyP : 0 < y * P := mul_pos hypos hPpos
  have htlt1 : x * b < 1 := by
    have h1 : b * (y - x) = 1 - x * b := by linear_combination hby
    have h2 : 0 < b * (y - x) := mul_pos hbpos (by linarith)
    linarith
  have hthalf : 1 / 2 < x * b := by
    have h1 : 0 < x * (b - a) := mul_pos hxpos (by linarith)
    have h2 : x * (b - a) = x * b - x * a := by ring
    linarith
  have hqh : 1 / 2 ≤ q := hq.ge_of_ge fl_half hthalf.le
  have hq1 : q ≤ 1 := hq.le_of_le fl_one htlt1.le
  have hPa : P / 2 * a = 1 / 2 := by linear_combination (1 / 2) * haP
  obtain ⟨k, hk⟩ := float_grid hq.1 (-(p:ℤ)) (by rw [eH, e1]; linarith)
  rw [e1] at hk
  have hkP1 : P / 2 ≤ k := by
    rw [hk] at hqh
    have h1 : P * ((k:ℚ) * a - 1 / 2) = k - P / 2 := by linear_combination (k:ℚ) * haP
    have h2 : 0 ≤ P * ((k:ℚ) * a - 1 / 2) := mul_nonneg hPpos.le (by linarith)
    linarith
  have hkP2 : (k:ℚ) ≤ P := by
    rw [hk] at hq1
    have h1 : P * (1 - (k:ℚ) * a) = P - k := by linear_combination (-(k:ℚ)) * haP
    have h2 : 0 ≤ P * (1 - (k:ℚ) * a) := mul_nonneg hPpos.le (by linarith)
    linarith
  have hqe := hq.err hp1 (-(p:ℤ)) (by
    rw [← hP, e1, abs_of_pos htpos]
    have : P * a = 1 := by linear_combination haP
    linarith)
  rw [e1, hk] at hqe
  have hqe' := abs_le.mp hqe
  have hY2' : Y < 2 ^ (p + 1) := by
    rw [pow_succ]
    have : (0:ℤ) < 2 ^ p := by positivity
    linarith
  obtain ⟨N1, hN1d⟩ : ∃ N : ℤ, N = X * 2 ^ (p + 1) - (2 * k + 1) * Y := ⟨_, rfl⟩
  obtain ⟨N2, hN2d⟩ : ∃ N : ℤ, N = X * 2 ^ (p + 1) - (2 * (k - 1) + 1) * Y := ⟨_, rfl⟩
  have cN1 : (N1:ℚ) = x * (2 * P) - (2 * k + 1) * y := by
    rw [hN1d, hx, hy, ← hPc]; push_cast; ring
  have cN2 : (N2:ℚ) = x * (2 * P) - (2 * k - 1) * y := by
    rw [hN2d, hx, hy, ← hPc]; push_cast; ring
  have i1 : (x * b - k * a - a / 2) * (2 * (y * P)) = x * (2 * P) - (2 * k + 1) * y := by
    linear_combination (2 * x * P) * hby - ((2 * k + 1) * y) * haP
  have i2 : (x * b - k * a + a / 2) * (2 * (y * P)) = x * (2 * P) - (2 * k - 1) * y := by
    linear_combination (2 * x * P) * hby - ((2 * k - 1) * y) * haP
  have habyP : (a * b / 2) * (2 * (y * P)) = 1 := by linear_combination (a * P) * hby + haP
  have hyP2 : 0 < 2 * (y * P) := by linarith
  have hN1 : N1 ≤ -2 := by
    have h1 : (N1:ℚ) ≤ 0 := by
      rw [cN1, ← i1]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hqe'.2]) hyP2.le
    have h2 : N1 ≤ 0 := by exact_mod_cast h1
    have h3 : N1 ≠ 0 := fun h0 =>
      odd_mul_ne_pow (X := X) hY0 hY2' (m := k) (by rw [hN1d] at h0; linear_combination h0)
    have h4 : N1 ≠ -1 := by rw [hN1d]; exact (hno (2 * k + 1)).2
    omega
  have hN2 : 2 ≤ N2 := by
    have h1 : (0:ℚ) ≤ (N2:ℚ) := by
      rw [cN2, ← i2]; exact mul_nonneg (by linarith [hqe'.1]) hyP2.le
    have h2 : 0 ≤ N2 := by exact_mod_cast h1
    have h3 : N2 ≠ 0 := fun h0 =>
      odd_mul_ne_pow (X := X) hY0 hY2' (m := k - 1) (by rw [hN2d] at h0; linear_combination h0)
    have h4 : N2 ≠ 1 := by rw [hN2d]; exact (hno (2 * (k - 1) + 1)).1
    omega
  have hN1q : x * (2 * P) - (2 * k + 1) * y ≤ -2 := by rw [← cN1]; exact_mod_cast hN1
  have hN2q : 2 ≤ x * (2 * P) - (2 * k - 1) * y := by rw [← cN2]; exact_mod_cast hN2
  have j1 : x * b - k * a - a / 2 = (x * (2 * P) - (2 * k + 1) * y) * (a * b / 2) := by
    rw [← i1]; linear_combination (-(x * b - k * a - a / 2)) * habyP
  have j2 : x * b - k * a + a / 2 = (x * (2 * P) - (2 * k - 1) * y) * (a * b / 2) := by
    rw [← i2]; linear_combination (-(x * b - k * a + a / 2)) * habyP
  have hab2 : 0 ≤ a * b / 2 := by linarith
  have u1 : x * b - k * a - a / 2 ≤ -(a * b) := by
    rw [j1]
    have := mul_le_mul_of_nonneg_right hN1q hab2
    linarith
  have u2 : a * b ≤ x * b - k * a + a / 2 := by
    rw [j2]
    have := mul_le_mul_of_nonneg_right hN2q hab2
    linarith
  have hfin := nearest_unique hp1 hq2 k (-(p:ℤ)) (by rw [eH]; exact hkP1)
    (by rw [← hP]; exact hkP2)
    (by rw [e1, abs_lt]; constructor <;> linarith [herr'.1, herr'.2])
    (by
      intro hkeq
      rw [eH] at hkeq
      rw [e1, hkeq, hPa]
      linarith [herr'.1])
  rw [e1] at hfin
  rw [hfin, hk]

/-- **Theorem A.** Correctness of Algorithm 2 on integer significands. -/
theorem alg2_core {p : ℕ} (hp : 2 ≤ p) (X Y : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hcand : Y ≤ X ∨ ∀ B : ℤ, X * 2 ^ (p + 1) - B * Y ≠ 1 ∧ X * 2 ^ (p + 1) - B * Y ≠ -1)
    {zh zl t1 q2 q : ℚ}
    (hzh : IsNearest p (1 / (Y:ℚ)) zh)
    (hzl : IsNearest p (1 / (Y:ℚ) - zh) zl)
    (ht1 : IsNearest p ((X:ℚ) * zl) t1)
    (hq2 : IsNearest p ((X:ℚ) * zh + t1) q2)
    (hq : IsNearest p ((X:ℚ) / (Y:ℚ)) q) : q2 = q := by
  have hp1 : 1 ≤ p := by omega
  have hY0 : 0 < Y := by
    have : (0:ℤ) < 2 ^ p := by positivity
    linarith
  obtain ⟨P, hP⟩ : ∃ P : ℚ, P = 2 ^ (p:ℤ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℚ, x = (X:ℚ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℚ, y = (Y:ℚ) := ⟨_, rfl⟩
  have hPc : ((2 ^ p : ℤ) : ℚ) = P := by rw [hP]; exact cast_two_pow p
  have hP4 : (4:ℚ) ≤ P := by
    have h1 : (2:ℚ) ^ (2:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [← hP] at h1
    norm_num at h1
    exact h1
  have hPpos : (0:ℚ) < P := by linarith
  have hx1 : P ≤ 2 * x := by
    have h1 : ((2 ^ p : ℤ) : ℚ) ≤ ((2 * X : ℤ) : ℚ) := by exact_mod_cast hX1
    rw [hPc] at h1; push_cast at h1; rw [hx]; exact h1
  have hx2 : x < P := by
    have h1 : (X:ℚ) < ((2 ^ p : ℤ) : ℚ) := by exact_mod_cast hX2
    rw [hPc] at h1; rw [hx]; exact h1
  have hy1 : P ≤ 2 * y := by
    have h1 : ((2 ^ p : ℤ) : ℚ) ≤ ((2 * Y : ℤ) : ℚ) := by exact_mod_cast hY1
    rw [hPc] at h1; push_cast at h1; rw [hy]; exact h1
  have hy2 : y < P := by
    have h1 : (Y:ℚ) < ((2 ^ p : ℤ) : ℚ) := by exact_mod_cast hY2
    rw [hPc] at h1; rw [hy]; exact h1
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℚ, a = P⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, b = y⁻¹ := ⟨_, rfl⟩
  have haP : a * P = 1 := by rw [ha]; exact inv_mul_cancel₀ hPpos.ne'
  have hby : b * y = 1 := by rw [hb]; exact inv_mul_cancel₀ hypos.ne'
  have hapos : 0 < a := by rw [ha]; exact inv_pos.mpr hPpos
  have hbpos : 0 < b := by rw [hb]; exact inv_pos.mpr hypos
  have hb2a : b ≤ 2 * a := by
    have h1 : 2 * a - b = a * b * (2 * y - P) := by linear_combination b * haP - 2 * a * hby
    have h2 : 0 ≤ a * b * (2 * y - P) := mul_nonneg (mul_pos hapos hbpos).le (by linarith)
    linarith
  have h1y : 1 / (Y:ℚ) = b := by rw [hb, hy, one_div]
  have hxy : (X:ℚ) / (Y:ℚ) = x * b := by rw [hb, hy, hx, div_eq_mul_inv]
  rw [h1y] at hzh hzl
  rw [← hx] at ht1 hq2
  rw [hxy] at hq
  have herr := err_bound hp1 hP haP hPpos hbpos hb2a hxpos hx2 hzh hzl ht1
  by_cases hYX : Y ≤ X
  · have hyx : y ≤ x := by rw [hx, hy]; exact_mod_cast hYX
    exact finish_ge hp X Y hY0 hY2 hP hx hy haP hby hP4 hx2 hy2 hy1 hyx herr hq2 hq
  · have hno := hcand.resolve_left hYX
    have hxy' : x < y := by
      have : X < Y := by omega
      rw [hx, hy]; exact_mod_cast this
    exact finish_lt hp X Y hY0 hY2 hno hP hx hy haP hby hP4 hx1 hy2 hxy' herr hq2 hq

end ExactFDiv
