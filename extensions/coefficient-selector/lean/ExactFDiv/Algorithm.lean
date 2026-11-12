/-
Exact division by an invariant floating-point divisor — the algorithm, end to end.

`efdSetup` and `efdDiv` follow `native/exact_fdiv.h` (`efd64_setup` / `efd64_div`, and the binary32
twins) branch for branch, in the IEEE model with round-to-nearest-even:

* setup: `y` must be a normal number; `zh = 1 ⊘ y` must be normal; `ρ = fma(-y, zh, 1)`; if `ρ` is a
  zero the divisor is a power of two (mode `exact`); otherwise `zl = ρ ⊘ y` must be a number with
  `|zl| ≥ 2·minNormal`, and the significand must pass `accept`; then mode `fma` with the
  thresholds `tlo`, `thi` computed from the binary exponent of `zl` exactly as the C does
  (`frexp`); anything else is mode `div`;
* division: mode `exact` multiplies by `zh`; mode `fma` uses the kernel when `tlo ≤ |x| < thi`
  and divides otherwise (NaN, infinities and zeros always divide); mode `div` divides.

**`efd_correct`: for every valid `x` and `y`, `efdDiv (efdSetup y) y x = div x y`.**
-/
import ExactFDiv.Checker

namespace ExactFDiv

theorem rneR_num {p : ℕ} {emin emax : ℤ} {t v : ℚ} (h : rneR p emin emax t = IEEE.num v) :
    v = rne p emin t := by
  unfold rneR at h
  split_ifs at h with h1 h2
  all_goals first | (cases h; done) | (injection h with h'; exact h'.symm)

theorem rneR_congr {p : ℕ} {emin emax : ℤ} {s q : ℚ} (hne : rne p emin s ≠ 0)
    (h : rne p emin s = rne p emin q) : rneR p emin emax s = rneR p emin emax q := by
  have hne' : rne p emin q ≠ 0 := h ▸ hne
  unfold rneR
  rw [if_neg hne, if_neg hne', h]

/-- Theorem B, item 1, with round-to-nearest-even and the verified check `accept` in place of
admissibility: covers every significand of `x`, including the candidate. -/
theorem kernel_eq_div_rne {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ}
    (hemin : emin + 2 * (p:ℤ) ≤ 1) (hemax : 0 ≤ emax)
    (R : ℚ → IEEE) (hRdef : R = rneR p emin emax)
    (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hacc : accept p Y = true)
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
  have hR : ∀ t, t ≠ 0 → RoundSpec p emin emax t (R t) := by
    intro t _; rw [hRdef]; exact rneR_spec hp1 emin emax t
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
  have ezh : zh = rneU p (1 / y) := by
    rw [← rne_eq_rneU hinvn]; rw [hRdef] at hzh; exact rneR_num hzh
  have ezl : zl = rneU p (1 / y - zh) := by
    rw [← rne_eq_rneU hvn]; rw [hRdef] at hzl; exact rneR_num hzl
  have et1 : t1 = rneU p (x * zl) := by
    rw [← rne_eq_rneU hlo]; rw [hRdef] at ht1R; exact rneR_num ht1R
  have hk := accept_sound hp X Y i j hX1 hX2 hY1 hY2 hacc hx hy
  unfold kernelU zlU zhU at hk
  rw [← ezh, ← ezl, ← et1] at hk
  rw [hRdef]
  have hs_ne : rne p emin (x * zh + t1) ≠ 0 := by
    intro h0
    have h3 := (rne_nearest hp1 emin (x * zh + t1)).le_abs fl_lam hsn
    rw [h0, abs_zero] at h3; linarith
  exact rneR_congr hs_ne (by rw [rne_eq_rneU hsn, rne_eq_rneU hqn, hk])

/-! ### Significands, thresholds, and the algorithm -/

/-- a finite nonzero float of the format -/
def ValidNum (p : ℕ) (emin emax : ℤ) (v : ℚ) : Prop :=
  v ≠ 0 ∧ IsFloatB p emin v ∧ |v| ≤ maxFloat p emax

/-- a datum of the format (NaN, infinities and zeros are always valid) -/
def Valid (p : ℕ) (emin emax : ℤ) : IEEE → Prop
  | .num v => ValidNum p emin emax v
  | _ => True

/-- the integer significand in `[2^(p-1), 2^p)` of a nonzero float -/
def sigOf (p : ℕ) (v : ℚ) : ℤ := ⌊|v| / 2 ^ (Int.log 2 |v| - (p:ℤ) + 1)⌋

theorem sigOf_spec {p : ℕ} (hp : 1 ≤ p) {v : ℚ} (hv : v ≠ 0) (hf : IsFloat p v) :
    (2:ℤ) ^ p ≤ 2 * sigOf p v ∧ sigOf p v < 2 ^ p ∧
    (v = sigOf p v * (2:ℚ) ^ (Int.log 2 |v| - (p:ℤ) + 1) ∨
     v = -(sigOf p v * (2:ℚ) ^ (Int.log 2 |v| - (p:ℤ) + 1))) := by
  obtain ⟨hlo, hhi⟩ := log_bounds hv
  obtain ⟨m, e, hm, hve⟩ := hf
  obtain ⟨E, hE⟩ : ∃ E, E = Int.log 2 |v| := ⟨_, rfl⟩
  rw [← hE] at hlo hhi ⊢
  have hsig_def : sigOf p v = ⌊|v| / 2 ^ (E - (p:ℤ) + 1)⌋ := by unfold sigOf; rw [hE]
  rw [hsig_def]
  obtain ⟨j, hj⟩ : ∃ j, j = E - (p:ℤ) + 1 := ⟨_, rfl⟩
  rw [← hj]
  have hmq : |(m:ℚ)| < 2 ^ (p:ℤ) := by
    rw [← cast_two_pow, ← Int.cast_abs]; exact_mod_cast hm
  have habs : |v| = |(m:ℚ)| * 2 ^ e := by rw [hve, abs_mul, abs_of_pos (two_zpow_pos e)]
  have hej : j ≤ e := by
    by_contra h
    push Not at h
    have h1 : |v| < 2 ^ (p:ℤ) * 2 ^ e := by
      rw [habs]; exact mul_lt_mul_of_pos_right hmq (two_zpow_pos e)
    have h2 : (2:ℚ) ^ (p:ℤ) * 2 ^ e ≤ 2 ^ E := by
      rw [← zpow_split]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, e = j + d := ⟨(e - j).toNat, by omega⟩
  have hjpos := two_zpow_pos j
  have hquot : |v| / 2 ^ j = ((|m| * 2 ^ d : ℤ) : ℚ) := by
    rw [habs, hd, zpow_split]; push_cast; rw [zpow_natCast]; field_simp
  rw [hquot, Int.floor_intCast]
  have hj1 : (2:ℚ) ^ E = 2 ^ ((p:ℤ) - 1) * 2 ^ j := by rw [← zpow_split]; congr 1; omega
  have hj2 : (2:ℚ) ^ (E + 1) = 2 ^ (p:ℤ) * 2 ^ j := by rw [← zpow_split]; congr 1; omega
  have b1 : 2 ^ ((p:ℤ) - 1) ≤ |v| / 2 ^ j := by rw [le_div_iff₀ hjpos, ← hj1]; exact hlo
  have b2 : |v| / 2 ^ j < 2 ^ (p:ℤ) := by rw [div_lt_iff₀ hjpos, ← hj2]; exact hhi
  rw [hquot] at b1 b2
  have hv' : |v| = ((|m| * 2 ^ d : ℤ) : ℚ) * 2 ^ j := by
    rw [← hquot]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have : ((2 ^ p : ℤ) : ℚ) ≤ ((2 * (|m| * 2 ^ d) : ℤ) : ℚ) := by
      rw [cast_two_pow]
      have e1 : (2:ℚ) ^ (p:ℤ) = 2 * 2 ^ ((p:ℤ) - 1) := by rw [zpow_pred']; ring
      rw [e1]; push_cast at b1 ⊢; linarith
    exact_mod_cast this
  · have : ((|m| * 2 ^ d : ℤ) : ℚ) < ((2 ^ p : ℤ) : ℚ) := by rw [cast_two_pow]; exact b2
    exact_mod_cast this
  · rcases le_or_gt 0 v with h0 | h0
    · left; rw [← hv', abs_of_nonneg h0]
    · right; rw [← hv', abs_of_neg h0]; ring

/-- `tlo`.  C computes `frexp(|zl|) = f * 2^e` with `e = log2|zl| + 1` (floor log) and sets
`tlo = 2^(max(emin, emin+p-1 - log2|zl|))` (binary64: `2^(-1021 - e)`, clamped at `2^-1074`). -/
def tloOf (p : ℕ) (emin : ℤ) (zl : ℚ) : ℚ := 2 ^ max emin (emin + (p:ℤ) - 1 - Int.log 2 |zl|)

/-- `thi`.  None (`+inf`) when `e <= 0`, i.e. `|zl| < 1`; otherwise `2^(emax+p-2 - log2|zl|)`
(binary64: `2^(1023 - e)`). -/
def thiOf (p : ℕ) (emax : ℤ) (zl : ℚ) : Option ℚ :=
  if Int.log 2 |zl| ≤ -1 then none else some (2 ^ (emax + (p:ℤ) - 2 - Int.log 2 |zl|))

theorem tloOf_spec {p : ℕ} {emin : ℤ} {zl : ℚ} (hzl : zl ≠ 0) :
    minNormal p emin ≤ tloOf p emin zl * |zl| := by
  have hb := (log_bounds hzl).1
  have h1 : (2:ℚ) ^ (emin + (p:ℤ) - 1 - Int.log 2 |zl|) ≤ tloOf p emin zl :=
    zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _)
  have h2 : minNormal p emin = 2 ^ (emin + (p:ℤ) - 1 - Int.log 2 |zl|) * 2 ^ Int.log 2 |zl| := by
    unfold minNormal; rw [← zpow_split, ← zpow_split]; congr 1; ring
  rw [h2]
  exact mul_le_mul h1 hb (two_zpow_pos _).le (le_trans (two_zpow_pos _).le h1)

theorem thiOf_some {p : ℕ} (hp : 1 ≤ p) {emax : ℤ} {zl t : ℚ} (hzl : zl ≠ 0)
    (h : thiOf p emax zl = some t) : t * |zl| ≤ maxFloat p emax := by
  unfold thiOf at h
  split_ifs at h with c
  injection h with ht
  rw [← ht]
  have hb := (log_bounds hzl).2
  have h1 : (2:ℚ) ^ (emax + (p:ℤ) - 2 - Int.log 2 |zl|) * |zl|
      ≤ 2 ^ (emax + (p:ℤ) - 2 - Int.log 2 |zl|) * 2 ^ (Int.log 2 |zl| + 1) :=
    mul_le_mul_of_nonneg_left hb.le (two_zpow_pos _).le
  have h2 : (2:ℚ) ^ (emax + (p:ℤ) - 2 - Int.log 2 |zl|) * 2 ^ (Int.log 2 |zl| + 1)
      = 2 ^ ((p:ℤ) - 1) * 2 ^ emax := by
    rw [← zpow_split, ← zpow_split]; congr 1; ring
  linarith [pow_le_maxFloat hp emax]

theorem thiOf_none {p : ℕ} {emax : ℤ} {zl : ℚ} (hzl : zl ≠ 0) (h : thiOf p emax zl = none) :
    |zl| ≤ 1 := by
  unfold thiOf at h
  split_ifs at h with c
  have hb := (log_bounds hzl).2
  have h1 : (2:ℚ) ^ (Int.log 2 |zl| + 1) ≤ 2 ^ (0:ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_zero] at h1
  linarith

/-- the three modes of `exact_fdiv.h` -/
inductive Mode where
  | div
  | exact (zh : ℚ)
  | fma (zh zl tlo : ℚ) (thi : Option ℚ)

/-- `efd_setup`, in the IEEE model with round-to-nearest-even -/
def efdSetup (p : ℕ) (emin emax : ℤ) (y : IEEE) : Mode :=
  match y with
  | .num yv =>
    if |yv| < minNormal p emin then .div else
    match div (rneR p emin emax) (.num 1) (.num yv) with
    | .num zh =>
      if |zh| < minNormal p emin then .div else
      match fma (rneR p emin emax) (.num (-yv)) (.num zh) (.num 1) with
      | .zero _ => .exact zh
      | .num ρ =>
        match div (rneR p emin emax) (.num ρ) (.num yv) with
        | .num zl =>
          if |zl| < 2 * minNormal p emin then .div
          else if accept p (sigOf p yv) then .fma zh zl (tloOf p emin zl) (thiOf p emax zl)
          else .div
        | _ => .div
      | _ => .div
    | _ => .div
  | _ => .div

/-- the guard `tlo <= |x| < thi` -/
def inRange (tlo : ℚ) (thi : Option ℚ) (v : ℚ) : Bool :=
  decide (tlo ≤ |v|) && (match thi with | none => true | some t => decide (|v| < t))

/-- `efd_div`, in the IEEE model with round-to-nearest-even -/
def efdDiv (p : ℕ) (emin emax : ℤ) (m : Mode) (y x : IEEE) : IEEE :=
  match m with
  | .div => div (rneR p emin emax) x y
  | .exact zh => mul (rneR p emin emax) x (.num zh)
  | .fma zh zl tlo thi =>
    match x with
    | .num xv =>
      if inRange tlo thi xv then
        fma (rneR p emin emax) x (.num zh) (mul (rneR p emin emax) x (.num zl))
      else div (rneR p emin emax) x y
    | _ => div (rneR p emin emax) x y

theorem inRange_spec {tlo v : ℚ} {thi : Option ℚ} (h : inRange tlo thi v = true) :
    tlo ≤ |v| ∧ ∀ t, thi = some t → |v| < t := by
  unfold inRange at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have h2 := h.2
  rw [ht] at h2
  simpa using h2

/-- **The algorithm divides.**  For every datum `y` and `x` of the format (NaN, infinities, zeros,
subnormals and overflow included), the guarded division with the precomputed setup returns
exactly the IEEE quotient `x / y` under round-to-nearest-even. -/
theorem efd_correct {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ} (hemin : emin + 2 * (p:ℤ) ≤ 1)
    (hemax : 0 ≤ emax) (y x : IEEE) (hy : Valid p emin emax y) (hx : Valid p emin emax x) :
    efdDiv p emin emax (efdSetup p emin emax y) y x = div (rneR p emin emax) x y := by
  have hp1 : 1 ≤ p := by omega
  have hR : ∀ t, t ≠ 0 → RoundSpec p emin emax t (rneR p emin emax t) :=
    fun t _ => rneR_spec hp1 emin emax t
  cases y with
  | nan => rfl
  | inf s => rfl
  | zero s => rfl
  | num yv =>
    obtain ⟨hyv0, hyf, -⟩ := hy
    obtain ⟨hY1, hY2, hyrep⟩ := sigOf_spec hp1 hyv0 hyf.isFloat
    dsimp only [efdSetup]
    by_cases hyn : |yv| < minNormal p emin
    · rw [if_pos hyn]; rfl
    rw [if_neg hyn]
    cases hzh : div (rneR p emin emax) (IEEE.num 1) (IEEE.num yv) with
    | nan => rfl
    | inf s => rfl
    | zero s => rfl
    | num zh =>
      dsimp only
      by_cases hzhn : |zh| < minNormal p emin
      · rw [if_pos hzhn]; rfl
      rw [if_neg hzhn]
      push Not at hzhn
      cases hρ : fma (rneR p emin emax) (IEEE.num (-yv)) (IEEE.num zh) (IEEE.num 1) with
      | nan => rfl
      | inf s => rfl
      | zero s =>
        dsimp only
        obtain ⟨-, h2⟩ := rho_computed hp hemin hemax (rneR p emin emax) hR (sigOf p yv) _ hY1 hY2
          hyrep hzh hzhn
        have h1 : yv * zh = 1 := by
          by_contra hne
          rw [h2 hne] at hρ
          cases hρ
        exact mul_inv_eq_div (rneR p emin emax) h1 x
      | num ρ =>
        dsimp only
        cases hzl : div (rneR p emin emax) (IEEE.num ρ) (IEEE.num yv) with
        | nan => rfl
        | inf s => rfl
        | zero s => rfl
        | num zl =>
          dsimp only
          by_cases hzln : |zl| < 2 * minNormal p emin
          · rw [if_pos hzln]; rfl
          rw [if_neg hzln]
          push Not at hzln
          by_cases hacc : accept p (sigOf p yv) = true
          swap
          · rw [if_neg hacc]; rfl
          rw [if_pos hacc]
          cases x with
          | nan => rfl
          | inf s => rfl
          | zero s => rfl
          | num xv =>
            obtain ⟨hxv0, hxf, hxmax⟩ := hx
            obtain ⟨hX1, hX2, hxrep⟩ := sigOf_spec hp1 hxv0 hxf.isFloat
            dsimp only [efdDiv]
            by_cases hin : inRange (tloOf p emin zl) (thiOf p emax zl) xv = true
            swap
            · rw [if_neg hin]
            rw [if_pos hin]
            obtain ⟨hlo1, hhi1⟩ := inRange_spec hin
            have hzl0 : zl ≠ 0 := by
              intro h0; rw [h0, abs_zero] at hzln; linarith [minNormal_pos p emin]
            have hguard : minNormal p emin ≤ |xv * zl| ∧ |xv * zl| ≤ maxFloat p emax := by
              cases hth : thiOf p emax zl with
              | none =>
                exact guards_imply_noupper (tloOf_spec hzl0) (thiOf_none hzl0 hth) hlo1 hxmax
              | some t =>
                exact guards_imply (tloOf_spec hzl0) (thiOf_some hp1 hzl0 hth) hlo1 (hhi1 t hth)
            have hzl' : div (rneR p emin emax) (fma (rneR p emin emax) (IEEE.num (-yv))
                (IEEE.num zh) (IEEE.num 1)) (IEEE.num yv) = IEEE.num zl := by rw [hρ]; exact hzl
            exact kernel_eq_div_rne hp hemin hemax (rneR p emin emax) rfl (sigOf p xv)
              (sigOf p yv) _ _ hX1 hX2 hY1 hY2 hacc hxrep hyrep hzh hzhn hzl' hzln hguard.1 hguard.2

end ExactFDiv

namespace ExactFDiv

/-- `efd_correct` for IEEE binary64 (quantum exponents: `emin = -1074`, `emax = 971`). -/
theorem efd_correct_binary64 (y x : IEEE) (hy : Valid 53 (-1074) 971 y)
    (hx : Valid 53 (-1074) 971 x) :
    efdDiv 53 (-1074) 971 (efdSetup 53 (-1074) 971 y) y x = div (rneR 53 (-1074) 971) x y :=
  efd_correct (by norm_num) (by norm_num) (by norm_num) y x hy hx

/-- `efd_correct` for IEEE binary32 (quantum exponents: `emin = -149`, `emax = 104`). -/
theorem efd_correct_binary32 (y x : IEEE) (hy : Valid 24 (-149) 104 y)
    (hx : Valid 24 (-149) 104 x) :
    efdDiv 24 (-149) 104 (efdSetup 24 (-149) 104 y) y x = div (rneR 24 (-149) 104) x y :=
  efd_correct (by norm_num) (by norm_num) (by norm_num) y x hy hx

end ExactFDiv
