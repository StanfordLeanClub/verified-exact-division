/-
Exact division by an invariant floating-point divisor — the setup phase.

For `y = ± Y * 2^j` (`2^(p-1) ≤ Y < 2^p`) and `zh` a nearest float of `1/y`:
* `setup_abs`: `|zh| ≥ 2^(-j-p)`, `|1/y - zh| ≤ 2^(-j-2p)`, `zh` has the sign of `y`, and
  `1 - y*zh = M * 2^(1-2p)` with `|M| < 2^p`: the residual `ρ = fma(-y, zh, 1)` is exactly
  representable as soon as `emin ≤ 1 - 2p`.
* `inv_ge_minNormal`: if the rounded reciprocal `zh` is a normal number, then `1/y` itself is at
  least the smallest normal number (so the rounding of `1/y` was an unbounded-exponent rounding).
-/
import ExactFDiv.IEEE

namespace ExactFDiv

theorem setup_pos {p : ℕ} (hp : 2 ≤ p) (Y j : ℤ) (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    {y zh : ℚ} (hy : y = Y * (2:ℚ) ^ j) (hzh : IsNearest p (1 / y) zh) :
    (2:ℚ) ^ (-j - (p:ℤ)) ≤ zh ∧ |1 / y - zh| ≤ 2 ^ (-j - 2 * (p:ℤ)) ∧
    ∃ M : ℤ, |M| < 2 ^ p ∧ 1 - y * zh = M * (2:ℚ) ^ (1 - 2 * (p:ℤ)) := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨P, hP⟩ : ∃ P : ℚ, P = 2 ^ (p:ℤ) := ⟨_, rfl⟩
  have hPc : ((2 ^ p : ℤ) : ℚ) = P := by rw [hP]; exact cast_two_pow p
  have hP4 : (4:ℚ) ≤ P := by
    have h1 : (2:ℚ) ^ (2:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [← hP] at h1
    norm_num at h1
    exact h1
  have hPpos : (0:ℚ) < P := by linarith
  obtain ⟨Yq, hYq⟩ : ∃ Yq : ℚ, Yq = (Y:ℚ) := ⟨_, rfl⟩
  have hYq1 : P ≤ 2 * Yq := by
    have h1 : ((2 ^ p : ℤ) : ℚ) ≤ ((2 * Y : ℤ) : ℚ) := by exact_mod_cast hY1
    rw [hPc] at h1; push_cast at h1; rw [hYq]; exact h1
  have hYq2 : Yq < P := by
    have h1 : (Y:ℚ) < ((2 ^ p : ℤ) : ℚ) := by exact_mod_cast hY2
    rw [hPc] at h1; rw [hYq]; exact h1
  have hYqpos : 0 < Yq := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 ^ (-j - 2 * (p:ℤ)) := ⟨_, rfl⟩
  obtain ⟨tj, htj⟩ : ∃ tj : ℚ, tj = 2 ^ j := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℚ, c3 = 2 ^ (1 - 2 * (p:ℤ)) := ⟨_, rfl⟩
  have hwpos : 0 < w := by rw [hw]; exact two_zpow_pos _
  have htjpos : 0 < tj := by rw [htj]; exact two_zpow_pos _
  have hc3pos : 0 < c3 := by rw [hc3]; exact two_zpow_pos _
  have e_j : tj * (w * (P * P)) = 1 := by
    rw [htj, hw, hP, ← zpow_split, ← zpow_split, ← zpow_split]
    have : j + (-j - 2 * (p:ℤ) + ((p:ℤ) + (p:ℤ))) = 0 := by ring
    rw [this, zpow_zero]
  have e3 : c3 * (P * P) = 2 := by
    rw [hc3, hP, ← zpow_split, ← zpow_split]
    have : 1 - 2 * (p:ℤ) + ((p:ℤ) + (p:ℤ)) = 1 := by ring
    rw [this, zpow_one]
  have e1 : (2:ℚ) ^ (-j - (p:ℤ)) = P * w := by
    rw [hP, hw, ← zpow_split]; congr 1; ring
  have e2 : (2:ℚ) ^ (-j - 2 * (p:ℤ) + 1) = 2 * w := by rw [zpow_succ', hw]; ring
  have eH : (2:ℚ) ^ ((p:ℤ) - 1) = P / 2 := by rw [zpow_pred', hP]
  rw [← htj] at hy
  have hypos : 0 < y := by rw [hy, ← hYq]; exact mul_pos hYqpos htjpos
  obtain ⟨b, hb⟩ : ∃ b : ℚ, b = 1 / y := ⟨_, rfl⟩
  rw [← hb] at hzh ⊢
  have hby : b * y = 1 := by rw [hb]; field_simp
  have hbpos : 0 < b := by rw [hb]; positivity
  have h1 : b * Yq * tj = 1 := by rw [hy, ← hYq] at hby; linear_combination hby
  have hbY : b * Yq = w * (P * P) := by
    linear_combination (-(b * Yq)) * e_j + (w * (P * P)) * h1
  have hwP : 0 < w * P := mul_pos hwpos hPpos
  have hb_hi : b ≤ 2 * w * P := by
    have h2 : b * Yq ≤ 2 * w * P * Yq := by
      have h3 : 0 ≤ w * P * (2 * Yq - P) := mul_nonneg hwP.le (by linarith)
      have h4 : w * P * (2 * Yq - P) = 2 * w * P * Yq - w * (P * P) := by ring
      linarith
    exact le_of_mul_le_mul_right h2 hYqpos
  have hb_lo : P * w ≤ b := by
    have h2 : P * w * Yq ≤ b * Yq := by
      have h3 : 0 ≤ w * P * (P - Yq) := mul_nonneg hwP.le (by linarith)
      have h4 : w * P * (P - Yq) = w * (P * P) - P * w * Yq := by ring
      linarith
    exact le_of_mul_le_mul_right h2 hYqpos
  -- zh ≥ P*w = 2^(-j-p)
  have fl_lo : IsFloat p (P * w) := ⟨1, -j - (p:ℤ), one_lt_two_pow hp1, by rw [e1]; simp⟩
  have hzh_lo : P * w ≤ zh := hzh.ge_of_ge fl_lo hb_lo
  -- grid and error
  obtain ⟨K, hK⟩ := float_grid hzh.1 (-j - 2 * (p:ℤ) + 1) (by
    rw [eH, e2]
    have : P / 2 * (2 * w) = P * w := by ring
    linarith)
  rw [e2] at hK
  have herr := hzh.err hp1 (-j - 2 * (p:ℤ) + 1) (by
    rw [← hP, e2, abs_of_pos hbpos]
    have : P * (2 * w) = 2 * w * P := by ring
    linarith)
  rw [e2] at herr
  have herr' : |b - zh| ≤ w := by linarith
  -- the residual
  obtain ⟨H, hH⟩ : ∃ H : ℤ, 2 * H = 2 ^ p := ⟨2 ^ (p - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  have hHq : 2 * (H:ℚ) = P := by
    have : ((2 * H : ℤ) : ℚ) = ((2 ^ p : ℤ) : ℚ) := by rw [hH]
    rw [hPc] at this; push_cast at this; exact this
  have hPP : (P * P) ≠ 0 := by positivity
  have hM : 1 - y * zh = ((H * 2 ^ p - Y * K : ℤ) : ℚ) * c3 := by
    have hc : ((H * 2 ^ p - Y * K : ℤ) : ℚ) = H * P - Yq * K := by
      rw [hYq, ← hPc]; push_cast; ring
    rw [hc, hy, hK, ← hYq]
    apply mul_right_cancel₀ hPP
    linear_combination (-2 * Yq * K) * e_j - ((H:ℚ) * P - Yq * K) * e3 - P * hHq
  refine ⟨by rw [e1]; exact hzh_lo, by rw [← hw]; exact herr', H * 2 ^ p - Y * K, ?_, by
    rw [← hc3]; exact hM⟩
  -- |M| < 2^p
  have h2 : 1 - y * zh = y * (b - zh) := by linear_combination -hby
  have h3 : |1 - y * zh| ≤ y * w := by
    rw [h2, abs_mul, abs_of_pos hypos]; exact mul_le_mul_of_nonneg_left herr' hypos.le
  rw [hM, abs_mul, abs_of_pos hc3pos] at h3
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℚ) ≤ P * P)
  have h5 : |((H * 2 ^ p - Y * K : ℤ) : ℚ)| * c3 * (P * P)
      = 2 * |((H * 2 ^ p - Y * K : ℤ) : ℚ)| := by
    linear_combination |((H * 2 ^ p - Y * K : ℤ) : ℚ)| * e3
  have h6 : y * w * (P * P) = Yq := by rw [hy, ← hYq]; linear_combination Yq * e_j
  rw [h5, h6] at h4
  have h7 : ((|H * 2 ^ p - Y * K| : ℤ) : ℚ) < ((2 ^ p : ℤ) : ℚ) := by
    rw [hPc, Int.cast_abs]; linarith
  exact_mod_cast h7

/-- `setup_pos` for a divisor of either sign, together with `sgn zh = sgn y`. -/
theorem setup_abs {p : ℕ} (hp : 2 ≤ p) (Y j : ℤ) (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    {y zh : ℚ} (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j)) (hzh : IsNearest p (1 / y) zh) :
    (2:ℚ) ^ (-j - (p:ℤ)) ≤ |zh| ∧ |1 / y - zh| ≤ 2 ^ (-j - 2 * (p:ℤ)) ∧ sgn zh = sgn y ∧
    ∃ M : ℤ, |M| < 2 ^ p ∧ 1 - y * zh = M * (2:ℚ) ^ (1 - 2 * (p:ℤ)) := by
  have hYpos : (0:ℚ) < (Y:ℚ) := by
    have h0 : (0:ℤ) < 2 ^ p := by positivity
    have : (0:ℤ) < Y := by linarith
    exact_mod_cast this
  have hmag : (0:ℚ) < (Y:ℚ) * 2 ^ j := mul_pos hYpos (two_zpow_pos j)
  have hlo : (0:ℚ) < 2 ^ (-j - (p:ℤ)) := two_zpow_pos _
  rcases hy with hy | hy
  · obtain ⟨h1, h2, M, hM1, hM2⟩ := setup_pos hp Y j hY1 hY2 hy hzh
    have hzpos : 0 < zh := lt_of_lt_of_le hlo h1
    have hypos : 0 < y := by rw [hy]; exact hmag
    refine ⟨le_trans h1 (le_abs_self zh), h2, ?_, M, hM1, hM2⟩
    simp only [sgn, decide_eq_decide]
    constructor <;> intro h <;> linarith
  · have hy' : -y = Y * (2:ℚ) ^ j := by rw [hy]; ring
    have hn := hzh.neg
    have e1 : -(1 / y) = 1 / -y := by rw [one_div, one_div, inv_neg]
    rw [e1] at hn
    obtain ⟨h1, h2, M, hM1, hM2⟩ := setup_pos hp Y j hY1 hY2 hy' hn
    have hzneg : zh < 0 := by linarith
    have hyneg : y < 0 := by linarith
    refine ⟨le_trans h1 (neg_le_abs zh), ?_, ?_, M, hM1, ?_⟩
    · have e2 : 1 / -y - -zh = -(1 / y - zh) := by rw [← e1]; ring
      rw [e2, abs_neg] at h2; exact h2
    · simp only [sgn, decide_eq_decide]
      constructor <;> intro _ <;> assumption
    · rw [← hM2]; ring

/-- If the rounded reciprocal of a positive float `y` is at least the smallest normal number,
then so is `1/y` (no float `y` has its reciprocal in the half-step just below `minNormal`). -/
theorem inv_ge_minNormal_pos {p : ℕ} (hp : 2 ≤ p) {emin : ℤ} {y zh : ℚ} (hy0 : 0 < y)
    (hyf : IsFloat p y) (hzh : IsNearestB p emin (1 / y) zh) (hn : minNormal p emin ≤ zh) :
    minNormal p emin ≤ 1 / y := by
  by_contra hlt
  push Not at hlt
  obtain ⟨P, hP⟩ : ∃ P : ℚ, P = 2 ^ (p:ℤ) := ⟨_, rfl⟩
  have hPc : ((2 ^ p : ℤ) : ℚ) = P := by rw [hP]; exact cast_two_pow p
  have hP4 : (4:ℚ) ≤ P := by
    have h1 : (2:ℚ) ^ (2:ℤ) ≤ 2 ^ (p:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [← hP] at h1
    norm_num at h1
    exact h1
  obtain ⟨Hq, hHq⟩ : ∃ Hq : ℚ, Hq = P / 2 := ⟨_, rfl⟩
  have hH2 : 2 ≤ Hq := by rw [hHq]; linarith
  have hHpos : 0 < Hq := by linarith
  have eH : (2:ℚ) ^ ((p:ℤ) - 1) = Hq := by rw [zpow_pred', ← hP, hHq]
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 ^ emin := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℚ, u = 2 ^ (2 - 2 * (p:ℤ) - emin) := ⟨_, rfl⟩
  have hwpos : 0 < w := by rw [hw]; exact two_zpow_pos _
  have hupos : 0 < u := by rw [hu]; exact two_zpow_pos _
  have hlam : minNormal p emin = Hq * w := by unfold minNormal; rw [eH, hw]
  -- (Hq u)(Hq w) = 1
  have e_uw : Hq * u * (Hq * w) = 1 := by
    rw [← eH, hu, hw, ← zpow_split, ← zpow_split, ← zpow_split]
    have : (p:ℤ) - 1 + (2 - 2 * (p:ℤ) - emin) + ((p:ℤ) - 1 + emin) = 0 := by ring
    rw [this, zpow_zero]
  rw [hlam] at hlt hn
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t = 1 / y := ⟨_, rfl⟩
  rw [← ht] at hlt hzh
  have hty : t * y = 1 := by rw [ht]; field_simp
  have htpos : 0 < t := by rw [ht]; positivity
  have hHw : 0 < Hq * w := mul_pos hHpos hwpos
  -- y > Hq * u
  have hy_gt : Hq * u < y := by
    have h1 : t * (Hq * u) < 1 := by
      have h2 : t * (Hq * u) * (Hq * w) = t := by linear_combination t * e_uw
      have h3 : t * (Hq * u) * (Hq * w) < 1 * (Hq * w) := by rw [h2]; linarith
      exact lt_of_mul_lt_mul_right h3 hHw.le
    have h4 : t * (Hq * u) < t * y := by rw [hty]; exact h1
    exact lt_of_mul_lt_mul_left h4 htpos.le
  -- y is on the grid of step u, strictly above Hq * u
  obtain ⟨k, hk⟩ := float_grid hyf (2 - 2 * (p:ℤ) - emin) (by rw [eH, ← hu]; exact hy_gt.le)
  rw [← hu] at hk
  obtain ⟨H, hH⟩ : ∃ H : ℤ, 2 * H = 2 ^ p := ⟨2 ^ (p - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  have hHc : (H:ℚ) = Hq := by
    have : ((2 * H : ℤ) : ℚ) = ((2 ^ p : ℤ) : ℚ) := by rw [hH]
    rw [hPc] at this; push_cast at this; rw [hHq]; linarith
  have hk_gt : Hq < k := by
    rw [hk] at hy_gt
    exact lt_of_mul_lt_mul_right hy_gt hupos.le
  have hk1 : Hq + 1 ≤ k := by
    rw [← hHc] at hk_gt ⊢
    have h1 : H < k := by exact_mod_cast hk_gt
    have h2 : H + 1 ≤ k := h1
    exact_mod_cast h2
  have hy_ge : (Hq + 1) * u ≤ y := by
    rw [hk]; exact mul_le_mul_of_nonneg_right hk1 hupos.le
  -- hence t < (Hq - 1/2) * w
  have ht_lt : t < (Hq - 1 / 2) * w := by
    by_contra h
    push Not at h
    have h1 : (Hq - 1 / 2) * w * ((Hq + 1) * u) ≤ t * y := by
      have hnn : 0 ≤ (Hq - 1 / 2) * w := mul_nonneg (by linarith) hwpos.le
      calc (Hq - 1 / 2) * w * ((Hq + 1) * u) ≤ (Hq - 1 / 2) * w * y :=
            mul_le_mul_of_nonneg_left hy_ge hnn
        _ ≤ t * y := mul_le_mul_of_nonneg_right h hy0.le
    rw [hty] at h1
    -- (Hq - 1/2)(Hq + 1) u w = 1 + (Hq/2 - 1/2) u w > 1
    have h2 : (Hq - 1 / 2) * w * ((Hq + 1) * u) = 1 + (Hq / 2 - 1 / 2) * (u * w) := by
      linear_combination e_uw
    have h3 : 0 < (Hq / 2 - 1 / 2) * (u * w) := mul_pos (by linarith) (mul_pos hupos hwpos)
    linarith
  -- the float g = (Hq - 1) * w is strictly closer to t than zh
  have hH2' : 2 ≤ H := by
    have : (2:ℚ) ≤ (H:ℚ) := by rw [hHc]; exact hH2
    exact_mod_cast this
  have fl_g : IsFloatB p emin ((Hq - 1) * w) := by
    refine ⟨H - 1, emin, ?_, le_refl _, ?_⟩
    · rw [abs_of_nonneg (by linarith)]
      have : (0:ℤ) < 2 ^ p := by positivity
      linarith
    · rw [← hHc, hw]; push_cast; ring
  have h1 := hzh.2 _ fl_g
  have h2 : |t - zh| = zh - t := by
    rw [abs_of_nonpos (by linarith)]; ring
  have h3 : |t - (Hq - 1) * w| < Hq * w - t := by
    rw [abs_lt]; constructor <;> linarith
  rw [h2] at h1
  linarith

/-- The same for a divisor of either sign. -/
theorem inv_ge_minNormal {p : ℕ} (hp : 2 ≤ p) {emin : ℤ} {y zh : ℚ} (hy0 : y ≠ 0)
    (hyf : IsFloat p y) (hzh : IsNearestB p emin (1 / y) zh) (hn : minNormal p emin ≤ |zh|) :
    minNormal p emin ≤ |1 / y| := by
  have hp1 : 1 ≤ p := by omega
  have hlam := minNormal_pos p emin
  have fl0 : IsFloatB p emin 0 := ⟨0, emin, by rw [abs_zero]; positivity, le_refl _, by simp⟩
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · -- y < 0: apply the positive case to -y, -zh
    have hn' := hzh.neg
    have e1 : -(1 / y) = 1 / -y := by rw [one_div, one_div, inv_neg]
    rw [e1] at hn'
    have hinvpos : 0 < 1 / -y := by
      have : 0 < -y := by linarith
      positivity
    have hz0 : 0 ≤ -zh := hn'.ge_of_ge fl0 hinvpos.le
    have hnz : minNormal p emin ≤ -zh := by
      rw [← abs_neg, abs_of_nonneg hz0] at hn; exact hn
    have h := inv_ge_minNormal_pos hp (by linarith : 0 < -y) hyf.neg hn' hnz
    rw [← e1] at h
    rw [← abs_neg]
    exact le_trans h (le_abs_self _)
  · have hinvpos : 0 < 1 / y := by positivity
    have hz0 : 0 ≤ zh := hzh.ge_of_ge fl0 hinvpos.le
    have hnz : minNormal p emin ≤ zh := by rw [abs_of_nonneg hz0] at hn; exact hn
    exact le_trans (inv_ge_minNormal_pos hp hpos hyf hzh hnz) (le_abs_self _)

end ExactFDiv
