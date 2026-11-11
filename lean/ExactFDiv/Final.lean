/-
Exact division by an invariant floating-point divisor — Theorem B, item 1, in the IEEE model.

`kernel_eq_div`: in a format with `emin ≤ 1 - 2p` and `emax ≥ 0`, with any rounding function `R`
satisfying `RoundSpec` (round to nearest, any tie rule, gradual underflow, overflow to infinity):
let the setup be computed with the format's own operations,

    zh = 1 ⊘ y,   ρ = fma(-y, zh, 1),   zl = ρ ⊘ y,

and assume `zh` is a normal number, `zl` is a number of magnitude at least twice the smallest
normal, and the significands of `x` and `y` are admissible.  Then for every finite nonzero `x`
with `minNormal ≤ |x * zl| ≤ maxFloat`,

    fma(x, zh, x ⊗ zl) = x ⊘ y

as IEEE data (both finite and equal, or both the same infinity).
-/
import ExactFDiv.Setup

namespace ExactFDiv

theorem isFloatB_pow {p : ℕ} (hp : 1 ≤ p) {emin e : ℤ} (he : emin ≤ e) :
    IsFloatB p emin (2 ^ ((p:ℤ) - 1) * 2 ^ e) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  refine ⟨2 ^ n, e, ?_, he, ?_⟩
  · rw [abs_of_nonneg (by positivity), pow_succ]
    have : (0:ℤ) < 2 ^ n := by positivity
    linarith
  · have e1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    rw [e1, ← cast_two_pow]

theorem pow_le_maxFloat {p : ℕ} (hp : 1 ≤ p) (emax : ℤ) :
    (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ emax ≤ maxFloat p emax := by
  unfold maxFloat
  have h2 : (2:ℚ) ^ (1:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_one] at h2
  have h1 : (2:ℚ) ^ ((p:ℤ) - 1) = 2 ^ (p:ℤ) / 2 := zpow_pred' _
  rw [h1]
  exact mul_le_mul_of_nonneg_right (by linarith) (two_zpow_pos emax).le

theorem one_le_maxFloat {p : ℕ} (hp : 1 ≤ p) {emax : ℤ} (hemax : 0 ≤ emax) :
    1 ≤ maxFloat p emax := by
  unfold maxFloat
  have h2 : (2:ℚ) ^ (1:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_one] at h2
  have h3 : (2:ℚ) ^ (0:ℤ) ≤ 2 ^ emax := zpow_le_zpow_right₀ (by norm_num) hemax
  rw [zpow_zero] at h3
  nlinarith

/-- **Theorem B, item 1.** -/
theorem kernel_eq_div {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ}
    (hemin : emin + 2 * (p:ℤ) ≤ 1) (hemax : 0 ≤ emax)
    (R : ℚ → IEEE) (hR : ∀ t, t ≠ 0 → RoundSpec p emin emax t (R t))
    (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hadm : Admissible p X Y)
    {x y zh zl : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : div R (IEEE.num 1) (IEEE.num y) = IEEE.num zh)
    (hzhn : minNormal p emin ≤ |zh|)
    (hzl : div R (fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1)) (IEEE.num y) = IEEE.num zl)
    (hzln : 2 * minNormal p emin ≤ |zl|)
    (hlo : minNormal p emin ≤ |x * zl|)
    (hhi : |x * zl| ≤ maxFloat p emax) :
    fma R (IEEE.num x) (IEEE.num zh) (mul R (IEEE.num x) (IEEE.num zl))
      = div R (IEEE.num x) (IEEE.num y) := by
  have hp1 : 1 ≤ p := by omega
  have hlam := minNormal_pos p emin
  have hYpos : (0:ℤ) < Y := by
    have h0 : (0:ℤ) < 2 ^ p := by positivity
    linarith
  have hYq : (0:ℚ) < (Y:ℚ) := by exact_mod_cast hYpos
  have hmagY : (0:ℚ) < (Y:ℚ) * 2 ^ j := mul_pos hYq (two_zpow_pos j)
  have hy0 : y ≠ 0 := by
    rcases hy with h | h
    · rw [h]; exact hmagY.ne'
    · rw [h]; exact neg_ne_zero.mpr hmagY.ne'
  have hyf : IsFloat p y := by
    have hYabs : |Y| < 2 ^ p := by rw [abs_of_pos hYpos]; exact hY2
    rcases hy with h | h
    · exact ⟨Y, j, hYabs, h⟩
    · exact ⟨-Y, j, by rwa [abs_neg], by rw [h]; push_cast; ring⟩
  -- zh is a nearest float of 1/y, in the unbounded sense
  have hzh1 : div R (IEEE.num 1) (IEEE.num y) = R (1 / y) := rfl
  rw [hzh1] at hzh
  have hinv0 : (1:ℚ) / y ≠ 0 := one_div_ne_zero hy0
  have hs1 := hR _ hinv0
  rw [hzh] at hs1
  obtain ⟨hzhB, -, -⟩ := hs1.num_inv
  have hinvn := inv_ge_minNormal hp hy0 hyf hzhB hzhn
  have hzhU : IsNearest p (1 / y) zh := hzhB.toNearest hp1 (Or.inl hinvn)
  obtain ⟨hzh_lo, hverr, -, M, hM1, hM2⟩ := setup_abs hp Y j hY1 hY2 hy hzhU
  -- the residual is exact
  have hfma1 : fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1)
      = if -y * zh + 1 = 0 then IEEE.zero false else R (-y * zh + 1) := rfl
  rw [hfma1] at hzl
  by_cases hρ : -y * zh + 1 = 0
  · rw [if_pos hρ] at hzl
    simp [div] at hzl
  rw [if_neg hρ] at hzl
  have hρeq : -y * zh + 1 = M * (2:ℚ) ^ (1 - 2 * (p:ℤ)) := by rw [← hM2]; ring
  have hρf : IsFloatB p emin (-y * zh + 1) := ⟨M, 1 - 2 * (p:ℤ), hM1, by linarith, hρeq⟩
  have hρmax : |-y * zh + 1| ≤ maxFloat p emax := by
    have hMq : |(M:ℚ)| < 2 ^ (p:ℤ) := by
      rw [← cast_two_pow, ← Int.cast_abs]; exact_mod_cast hM1
    have h2p : (2:ℚ) ^ (p:ℤ) * 2 ^ (1 - 2 * (p:ℤ)) ≤ 1 := by
      rw [← zpow_split]
      have h := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2)
        (by omega : (p:ℤ) + (1 - 2 * (p:ℤ)) ≤ 0)
      rw [zpow_zero] at h; exact h
    rw [hρeq, abs_mul, abs_of_pos (two_zpow_pos _)]
    have h3 : |(M:ℚ)| * 2 ^ (1 - 2 * (p:ℤ)) ≤ 2 ^ (p:ℤ) * 2 ^ (1 - 2 * (p:ℤ)) :=
      mul_le_mul_of_nonneg_right hMq.le (two_zpow_pos _).le
    linarith [one_le_maxFloat hp1 hemax]
  have hρR : R (-y * zh + 1) = IEEE.num (-y * zh + 1) := (hR _ hρ).of_float hρf hρ hρmax
  rw [hρR] at hzl
  have hzl1 : div R (IEEE.num (-y * zh + 1)) (IEEE.num y) = R ((-y * zh + 1) / y) := rfl
  rw [hzl1] at hzl
  have hv : (-y * zh + 1) / y = 1 / y - zh := by field_simp; ring
  rw [hv] at hzl
  have hv0 : 1 / y - zh ≠ 0 := by rw [← hv]; exact div_ne_zero hρ hy0
  have hs2 := hR _ hv0
  rw [hzl] at hs2
  obtain ⟨hzlB, -, -⟩ := hs2.num_inv
  have fl_lam : IsFloatB p emin (minNormal p emin) := isFloatB_minNormal hp1 emin
  have hvn : minNormal p emin ≤ |1 / y - zh| := by
    by_contra h
    push Not at h
    have h1 := hzlB.abs_le fl_lam h.le
    linarith
  have hzlU : IsNearest p (1 / y - zh) zl := hzlB.toNearest hp1 (Or.inl hvn)
  -- the correction term x ⊗ zl is finite, nonzero and a nearest float of x * zl
  have hmul : mul R (IEEE.num x) (IEEE.num zl) = R (x * zl) := rfl
  have hxzl0 : x * zl ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hlo; linarith
  obtain ⟨t1, ht1B, hc3⟩ := hR _ hxzl0
  have hee : emin ≤ emax := by linarith
  have fl_hi : IsFloatB p emin (maxFloat p emax) := by
    refine ⟨2 ^ p - 1, emax, ?_, hee, ?_⟩
    · have : (0:ℤ) < 2 ^ p := by positivity
      rw [abs_of_nonneg (by omega)]; omega
    · unfold maxFloat; push_cast; rw [zpow_natCast]
  have ht1lo := ht1B.le_abs fl_lam hlo
  have ht1hi := ht1B.abs_le fl_hi hhi
  have ht1R : R (x * zl) = IEEE.num t1 := by
    rcases hc3 with ⟨hz, -⟩ | ⟨-, -, hr⟩ | ⟨hgt, -⟩
    · rw [hz, abs_zero] at ht1lo; linarith
    · exact hr
    · linarith
  have ht1U : IsNearest p (x * zl) t1 := ht1B.toNearest hp1 (Or.inl hlo)
  -- magnitudes: everything is far above the smallest normal number
  obtain ⟨P, hP⟩ : ∃ P : ℚ, P = 2 ^ (p:ℤ) := ⟨_, rfl⟩
  have hP4 : (4:ℚ) ≤ P := by
    have h1 : (2:ℚ) ^ (2:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [← hP] at h1
    norm_num at h1
    exact h1
  obtain ⟨W, hW⟩ : ∃ W : ℚ, W = 2 ^ (-j - 2 * (p:ℤ)) := ⟨_, rfl⟩
  have hWpos : 0 < W := by rw [hW]; exact two_zpow_pos _
  have ePW : (2:ℚ) ^ (-j - (p:ℤ)) = P * W := by
    rw [hP, hW, ← zpow_split]; congr 1; ring
  rw [ePW] at hzh_lo
  rw [← hW] at hverr
  have flW : IsFloat p W := ⟨1, -j - 2 * (p:ℤ), one_lt_two_pow hp1, by rw [hW]; simp⟩
  have hverr' := abs_le.mp hverr
  have hzl_le : |zl| ≤ W :=
    abs_le.mpr ⟨hzlU.ge_of_ge flW.neg hverr'.1, hzlU.le_of_le flW hverr'.2⟩
  obtain ⟨ax, hax⟩ : ∃ ax : ℚ, ax = |x| := ⟨_, rfl⟩
  have hax0 : 0 ≤ ax := by rw [hax]; exact abs_nonneg x
  have hxzl : |x * zl| ≤ ax * W := by
    rw [abs_mul, ← hax]; exact mul_le_mul_of_nonneg_left hzl_le hax0
  have hxzh : ax * (P * W) ≤ |x * zh| := by
    rw [abs_mul, ← hax]; exact mul_le_mul_of_nonneg_left hzh_lo hax0
  have fl0 : IsFloat p 0 := ⟨0, 0, by rw [abs_zero]; positivity, by simp⟩
  have ht1abs : |t1| ≤ 2 * |x * zl| := by
    have h1 := ht1U.2 0 fl0
    rw [sub_zero] at h1
    have h2 : |t1| ≤ |x * zl| + |x * zl - t1| := by
      have h3 := abs_sub (x * zl) (x * zl - t1)
      rwa [sub_sub_cancel] at h3
    linarith
  have hs_lower : |x * zh| ≤ |x * zh + t1| + |t1| := by
    have h3 := abs_sub (x * zh + t1) t1
    rwa [add_sub_cancel_right] at h3
  have haxW : minNormal p emin ≤ ax * W := le_trans hlo hxzl
  have hPW : ax * (P * W) = P * (ax * W) := by ring
  have hsn : minNormal p emin ≤ |x * zh + t1| := by
    have h1 : 4 * (ax * W) ≤ P * (ax * W) :=
      mul_le_mul_of_nonneg_right hP4 (mul_nonneg hax0 hWpos.le)
    linarith
  have hs0 : x * zh + t1 ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hsn; linarith
  have hinv_lo : 3 * W ≤ |1 / y| := by
    have h1 : |zh| ≤ |1 / y| + |1 / y - zh| := by
      have h3 := abs_sub (1 / y) (1 / y - zh)
      rwa [sub_sub_cancel] at h3
    have h2 : 4 * W ≤ P * W := mul_le_mul_of_nonneg_right hP4 hWpos.le
    linarith
  have hqn : minNormal p emin ≤ |x / y| := by
    have h1 : x / y = x * (1 / y) := by rw [mul_one_div]
    rw [h1, abs_mul, ← hax]
    have h2 : ax * (3 * W) ≤ ax * |1 / y| := mul_le_mul_of_nonneg_left hinv_lo hax0
    have h3 : 0 ≤ ax * W := mul_nonneg hax0 hWpos.le
    linarith
  have hq0 : x / y ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hqn; linarith
  -- both sides are roundings of reals with the same unique nearest float
  have hfma2 : fma R (IEEE.num x) (IEEE.num zh) (IEEE.num t1)
      = if x * zh + t1 = 0 then IEEE.zero false else R (x * zh + t1) := rfl
  have hdiv : div R (IEEE.num x) (IEEE.num y) = R (x / y) := rfl
  rw [hmul, ht1R, hfma2, if_neg hs0, hdiv]
  refine (hR _ hs0).eq_of_unique (hR _ hq0) (fun f1 f2 h1 h2 => ?_)
  have h1U := h1.toNearest hp1 (Or.inl hsn)
  have h2U := h2.toNearest hp1 (Or.inl hqn)
  refine ⟨alg2_float hp X Y i j hX1 hX2 hY1 hY2 hadm hx hy hzhU hzlU ht1U h1U h2U, ?_⟩
  intro h0
  have h3 := h1.le_abs fl_lam hsn
  rw [h0, abs_zero] at h3
  linarith

/-- Theorem B, item 1, for divisors with an even significand: no per-divisor check is needed. -/
theorem kernel_eq_div_even {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ}
    (hemin : emin + 2 * (p:ℤ) ≤ 1) (hemax : 0 ≤ emax)
    (R : ℚ → IEEE) (hR : ∀ t, t ≠ 0 → RoundSpec p emin emax t (R t))
    (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p) (hYeven : 2 ∣ Y)
    {x y zh zl : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : div R (IEEE.num 1) (IEEE.num y) = IEEE.num zh)
    (hzhn : minNormal p emin ≤ |zh|)
    (hzl : div R (fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1)) (IEEE.num y) = IEEE.num zl)
    (hzln : 2 * minNormal p emin ≤ |zl|)
    (hlo : minNormal p emin ≤ |x * zl|)
    (hhi : |x * zl| ≤ maxFloat p emax) :
    fma R (IEEE.num x) (IEEE.num zh) (mul R (IEEE.num x) (IEEE.num zl))
      = div R (IEEE.num x) (IEEE.num y) :=
  kernel_eq_div hp hemin hemax R hR X Y i j hX1 hX2 hY1 hY2 (admissible_of_even X Y hYeven)
    hx hy hzh hzhn hzl hzln hlo hhi

/-- The C guards imply the real-valued hypotheses of `kernel_eq_div`: if `tlo * |zl| ≥ minNormal`
and `thi * |zl| ≤ maxFloat` (or there is no upper guard and `|zl| ≤ 1`, while `|x| ≤ maxFloat`),
then `tlo ≤ |x| < thi` gives `minNormal ≤ |x * zl| ≤ maxFloat`. -/
theorem guards_imply {p : ℕ} {emin emax : ℤ} {x zl tlo thi : ℚ}
    (hlo : minNormal p emin ≤ tlo * |zl|) (hthi : thi * |zl| ≤ maxFloat p emax)
    (hx1 : tlo ≤ |x|) (hx2 : |x| < thi) :
    minNormal p emin ≤ |x * zl| ∧ |x * zl| ≤ maxFloat p emax := by
  rw [abs_mul]
  have hz := abs_nonneg zl
  constructor
  · exact le_trans hlo (mul_le_mul_of_nonneg_right hx1 hz)
  · exact le_trans (mul_le_mul_of_nonneg_right hx2.le hz) hthi

theorem guards_imply_noupper {p : ℕ} {emin emax : ℤ} {x zl tlo : ℚ}
    (hlo : minNormal p emin ≤ tlo * |zl|) (hzl1 : |zl| ≤ 1)
    (hx1 : tlo ≤ |x|) (hx2 : |x| ≤ maxFloat p emax) :
    minNormal p emin ≤ |x * zl| ∧ |x * zl| ≤ maxFloat p emax := by
  rw [abs_mul]
  have hz := abs_nonneg zl
  constructor
  · exact le_trans hlo (mul_le_mul_of_nonneg_right hx1 hz)
  · have h1 : |x| * |zl| ≤ |x| * 1 := mul_le_mul_of_nonneg_left hzl1 (abs_nonneg x)
    linarith

/-- The C test `rho == 0.0` decides `y * zh = 1`: in the setup of `kernel_eq_div`, the computed
residual `fma(-y, zh, 1)` is a zero exactly when `y * zh = 1`, and otherwise the exact residual. -/
theorem rho_computed {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ}
    (hemin : emin + 2 * (p:ℤ) ≤ 1) (hemax : 0 ≤ emax)
    (R : ℚ → IEEE) (hR : ∀ t, t ≠ 0 → RoundSpec p emin emax t (R t))
    (Y j : ℤ) (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    {y zh : ℚ} (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : div R (IEEE.num 1) (IEEE.num y) = IEEE.num zh)
    (hzhn : minNormal p emin ≤ |zh|) :
    (y * zh = 1 → fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1) = IEEE.zero false) ∧
    (y * zh ≠ 1 → fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1) = IEEE.num (1 - y * zh)) := by
  have hp1 : 1 ≤ p := by omega
  have hYpos : (0:ℤ) < Y := by
    have h0 : (0:ℤ) < 2 ^ p := by positivity
    linarith
  have hYq : (0:ℚ) < (Y:ℚ) := by exact_mod_cast hYpos
  have hmagY : (0:ℚ) < (Y:ℚ) * 2 ^ j := mul_pos hYq (two_zpow_pos j)
  have hy0 : y ≠ 0 := by
    rcases hy with h | h
    · rw [h]; exact hmagY.ne'
    · rw [h]; exact neg_ne_zero.mpr hmagY.ne'
  have hyf : IsFloat p y := by
    have hYabs : |Y| < 2 ^ p := by rw [abs_of_pos hYpos]; exact hY2
    rcases hy with h | h
    · exact ⟨Y, j, hYabs, h⟩
    · exact ⟨-Y, j, by rwa [abs_neg], by rw [h]; push_cast; ring⟩
  have hzh1 : div R (IEEE.num 1) (IEEE.num y) = R (1 / y) := rfl
  rw [hzh1] at hzh
  have hs1 := hR _ (one_div_ne_zero hy0)
  rw [hzh] at hs1
  obtain ⟨hzhB, -, -⟩ := hs1.num_inv
  have hzhU : IsNearest p (1 / y) zh :=
    hzhB.toNearest hp1 (Or.inl (inv_ge_minNormal hp hy0 hyf hzhB hzhn))
  obtain ⟨-, -, -, M, hM1, hM2⟩ := setup_abs hp Y j hY1 hY2 hy hzhU
  have hfma1 : fma R (IEEE.num (-y)) (IEEE.num zh) (IEEE.num 1)
      = if -y * zh + 1 = 0 then IEEE.zero false else R (-y * zh + 1) := rfl
  have he : -y * zh + 1 = 1 - y * zh := by ring
  rw [hfma1, he]
  constructor
  · intro h1; rw [if_pos (by rw [h1]; ring)]
  · intro h1
    have hρ : 1 - y * zh ≠ 0 := fun h => h1 (by linarith)
    rw [if_neg hρ]
    have hρf : IsFloatB p emin (1 - y * zh) := ⟨M, 1 - 2 * (p:ℤ), hM1, by linarith, hM2⟩
    have hρmax : |1 - y * zh| ≤ maxFloat p emax := by
      have hMq : |(M:ℚ)| < 2 ^ (p:ℤ) := by
        rw [← cast_two_pow, ← Int.cast_abs]; exact_mod_cast hM1
      have h2p : (2:ℚ) ^ (p:ℤ) * 2 ^ (1 - 2 * (p:ℤ)) ≤ 1 := by
        rw [← zpow_split]
        have h := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2)
          (by omega : (p:ℤ) + (1 - 2 * (p:ℤ)) ≤ 0)
        rw [zpow_zero] at h; exact h
      rw [hM2, abs_mul, abs_of_pos (two_zpow_pos _)]
      have h3 : |(M:ℚ)| * 2 ^ (1 - 2 * (p:ℤ)) ≤ 2 ^ (p:ℤ) * 2 ^ (1 - 2 * (p:ℤ)) :=
        mul_le_mul_of_nonneg_right hMq.le (two_zpow_pos _).le
      linarith [one_le_maxFloat hp1 hemax]
    exact (hR _ hρ).of_float hρf hρ hρmax

end ExactFDiv
