/-
Exact division by an invariant floating-point divisor — a verified per-divisor check.

`accept p Y` is a computable Boolean on the integer significand `Y` of the divisor.  For an
odd `Y` it computes the two candidate significands `X₊ = (2^(p+1))⁻¹ mod Y` and `X₋ = Y - X₊`
(the only `X` for which Theorem A does not apply), and for each one in `[2^(p-1), Y)` it
evaluates the kernel *exactly*, with round-to-nearest-even, and compares it with the correctly
rounded quotient.  This is the check `efd64_bad_significand` performs in hardware arithmetic.

`accept_sound`: if `accept p Y = true`, then for every nonzero `x` and every divisor `y` with
significand `Y` (any signs, any exponents) the kernel with round-to-nearest-even returns the
round-to-nearest-even quotient.  This covers the candidate, which Theorem A alone cannot.

Everything here is in the unbounded-exponent model; `rneU` is round-to-nearest-even there, and
`rne_eq_rneU` says the format's `rne` agrees with it in the normal range.
-/
import ExactFDiv.RNE

namespace ExactFDiv

/-! ### Round-to-nearest-even with unbounded exponent -/

/-- round-to-nearest-even with unbounded exponent range -/
def rneU (p : ℕ) (t : ℚ) : ℚ :=
  (rhe (t / 2 ^ (Int.log 2 |t| - (p:ℤ) + 1)) : ℚ) * 2 ^ (Int.log 2 |t| - (p:ℤ) + 1)

theorem rne_eq_rneU_of_le {p : ℕ} {emin : ℤ} {t : ℚ} (h : emin ≤ Int.log 2 |t| - (p:ℤ) + 1) :
    rne p emin t = rneU p t := by
  unfold rne rneU rexp
  rw [max_eq_right h]

theorem minNormal_le_log {p : ℕ} {emin : ℤ} {t : ℚ} (h : minNormal p emin ≤ |t|) :
    emin ≤ Int.log 2 |t| - (p:ℤ) + 1 := by
  have hpos : 0 < |t| := lt_of_lt_of_le (minNormal_pos p emin) h
  have h1 : ((2:ℕ):ℚ) ^ ((p:ℤ) - 1 + emin) ≤ |t| := by
    push_cast
    rw [zpow_split]; unfold minNormal at h; exact h
  have h2 := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp h1
  omega

/-- in the normal range the format's rounding is the unbounded one -/
theorem rne_eq_rneU {p : ℕ} {emin : ℤ} {t : ℚ} (h : minNormal p emin ≤ |t|) :
    rne p emin t = rneU p t := rne_eq_rneU_of_le (minNormal_le_log h)

theorem rneU_nearest {p : ℕ} (hp : 1 ≤ p) (t : ℚ) : IsNearest p t (rneU p t) := by
  by_cases ht : t = 0
  · subst ht
    have : rneU p 0 = 0 := by simp [rneU, rhe]
    rw [this]
    refine ⟨⟨0, 0, by rw [abs_zero]; positivity, by simp⟩, fun g _ => ?_⟩
    simp
  set emin := Int.log 2 |t| - (p:ℤ) + 1 with hemin
  have h1 := rne_nearest hp emin t
  rw [rne_eq_rneU_of_le (le_refl _)] at h1
  apply h1.toNearest hp
  left
  unfold minNormal
  rw [← zpow_split]
  have := (log_bounds ht).1
  calc (2:ℚ) ^ ((p:ℤ) - 1 + emin) = 2 ^ Int.log 2 |t| := by congr 1; omega
    _ ≤ |t| := this

theorem log_mul_zpow {r : ℚ} (hr : 0 < r) (k : ℤ) :
    Int.log 2 (r * 2 ^ k) = Int.log 2 r + k := by
  have hrk : 0 < r * 2 ^ k := mul_pos hr (two_zpow_pos k)
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hr
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
  push_cast at h1 h2
  apply le_antisymm
  · have : r * 2 ^ k < ((2:ℕ):ℚ) ^ (Int.log 2 r + k + 1) := by
      push_cast
      rw [show Int.log 2 r + k + 1 = (Int.log 2 r + 1) + k by ring, zpow_split]
      exact mul_lt_mul_of_pos_right h2 (two_zpow_pos k)
    have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hrk).mp this
    omega
  · have : ((2:ℕ):ℚ) ^ (Int.log 2 r + k) ≤ r * 2 ^ k := by
      push_cast
      rw [zpow_split]
      exact mul_le_mul_of_nonneg_right h1 (two_zpow_pos k).le
    exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hrk).mp this

/-- `rneU` commutes with a sign and a power of two -/
theorem rneU_smul (p : ℕ) {s : ℚ} (hs : s = 1 ∨ s = -1) (t : ℚ) (k : ℤ) :
    rneU p (s * t * 2 ^ k) = s * rneU p t * 2 ^ k := by
  by_cases ht : t = 0
  · subst ht; simp [rneU, rhe]
  have habs : |s * t * 2 ^ k| = |t| * 2 ^ k := by
    rw [abs_mul, abs_mul, abs_of_pos (two_zpow_pos k)]
    rcases hs with h | h <;> rw [h] <;> simp
  have hlog : Int.log 2 |s * t * 2 ^ k| = Int.log 2 |t| + k := by
    rw [habs]; exact log_mul_zpow (abs_pos.mpr ht) k
  unfold rneU
  rw [hlog]
  obtain ⟨e, he0⟩ : ∃ e : ℤ, e = Int.log 2 |t| - (p:ℤ) + 1 := ⟨_, rfl⟩
  have he : Int.log 2 |t| + k - (p:ℤ) + 1 = e + k := by rw [he0]; ring
  rw [he, ← he0]
  have hz : (2:ℚ) ^ (e + k) = 2 ^ e * 2 ^ k := zpow_split e k
  have hq : s * t * 2 ^ k / 2 ^ (e + k) = s * (t / 2 ^ e) := by
    rw [hz]; field_simp
  rw [hq, hz]
  rcases hs with h | h
  · rw [h, one_mul, one_mul]; ring
  · rw [h, show (-1) * (t / 2 ^ e) = -(t / 2 ^ e) by ring, rhe_neg]
    push_cast; ring

/-! ### The kernel in the unbounded model, and the check -/

/-- high part of the reciprocal -/
def zhU (p : ℕ) (y : ℚ) : ℚ := rneU p (1 / y)
/-- low part of the reciprocal -/
def zlU (p : ℕ) (y : ℚ) : ℚ := rneU p (1 / y - zhU p y)
/-- the kernel `RN(x*zh + RN(x*zl))` with round-to-nearest-even -/
def kernelU (p : ℕ) (x y : ℚ) : ℚ := rneU p (x * zhU p y + rneU p (x * zlU p y))

/-- the candidate for sign `+1`: `(2^(p+1))⁻¹ mod Y` -/
def candP (p : ℕ) (Y : ℤ) : ℤ := Nat.gcdA (2 ^ (p + 1)) Y.toNat % Y

/-- is the kernel correct at significand `X` (or is `X` out of the range where it matters)? -/
def okAt (p : ℕ) (X Y : ℤ) : Bool :=
  !(decide ((2:ℤ) ^ p ≤ 2 * X) && decide (X < Y)) ||
    decide (kernelU p (X:ℚ) (Y:ℚ) = rneU p ((X:ℚ) / (Y:ℚ)))

/-- **the per-divisor check** -/
def accept (p : ℕ) (Y : ℤ) : Bool :=
  decide (Y % 2 = 0) || (okAt p (candP p Y) Y && okAt p (Y - candP p Y) Y)

theorem candP_spec {p : ℕ} {Y : ℤ} (hY0 : 1 < Y) (hYodd : Y % 2 = 1) :
    0 ≤ candP p Y ∧ candP p Y < Y ∧ ∃ B : ℤ, candP p Y * 2 ^ (p + 1) - B * Y = 1 := by
  have hYn : ((Y.toNat : ℕ) : ℤ) = Y := Int.toNat_of_nonneg (by omega)
  have hcop : Nat.Coprime (2 ^ (p + 1)) Y.toNat := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    have : Y.toNat % 2 = 1 := by omega
    exact Nat.odd_iff.mpr this
  have hg := Nat.gcd_eq_gcd_ab (2 ^ (p + 1)) Y.toNat
  rw [hcop] at hg
  push_cast at hg
  rw [hYn] at hg
  refine ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), ?_⟩
  refine ⟨-(Nat.gcdB (2 ^ (p + 1)) Y.toNat) - (Nat.gcdA (2 ^ (p + 1)) Y.toNat / Y) * 2 ^ (p + 1), ?_⟩
  unfold candP
  have hdiv := Int.emod_def (Nat.gcdA (2 ^ (p + 1)) Y.toNat) Y
  linear_combination (2 ^ (p + 1) : ℤ) * hdiv - hg

/-- an inadmissible significand is one of the two candidates -/
theorem inadmissible_is_cand {p : ℕ} (hp : 2 ≤ p) {X Y : ℤ}
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hna : ¬ Admissible p X Y) :
    Y % 2 = 1 ∧ (X = candP p Y ∨ X = Y - candP p Y) := by
  have hYodd : Y % 2 = 1 := by
    by_contra h
    exact hna (admissible_of_even X Y ⟨Y / 2, by omega⟩)
  have h4 : (4:ℤ) ≤ 2 ^ p := by
    calc (4:ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hY0 : 1 < Y := by omega
  have hX0 : 0 < X := by omega
  unfold Admissible at hna
  push Not at hna
  obtain ⟨hXY, B, hB⟩ := hna
  obtain ⟨c0, c1, B', hB'⟩ := candP_spec (p := p) hY0 hYodd
  have hYnd : ¬ 2 ∣ Y := by omega
  refine ⟨hYodd, ?_⟩
  by_cases h1 : X * 2 ^ (p + 1) - B * Y = 1
  · left
    exact candidate_unique hYnd (by omega) hX0.le hXY c0 c1 h1 hB'
  · right
    have h2 := hB h1
    have e2 : (Y - candP p Y) * 2 ^ (p + 1) - (2 ^ (p + 1) - B') * Y = -1 := by
      linear_combination -hB'
    have hc0 : candP p Y ≠ 0 := by
      intro h
      rw [h, zero_mul, zero_sub] at hB'
      have hd : Y ∣ 1 := ⟨-B', by linarith⟩
      have := Int.le_of_dvd (by norm_num) hd
      omega
    exact candidate_unique hYnd (by omega) hX0.le hXY (by omega) (by omega) h2 e2

/-- the kernel and the quotient in the unbounded model transform alike under signs and powers
of two of the operands -/
theorem kernelU_smul (p : ℕ) {sx sy : ℚ} (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (X Y : ℚ) (hY : Y ≠ 0) (i j : ℤ) :
    kernelU p (sx * X * 2 ^ i) (sy * Y * 2 ^ j) = (sx * sy) * kernelU p X Y * 2 ^ (i - j) ∧
    rneU p ((sx * X * 2 ^ i) / (sy * Y * 2 ^ j)) = (sx * sy) * rneU p (X / Y) * 2 ^ (i - j) := by
  have hsy2 : sy * sy = 1 := by rcases hsy with h | h <;> rw [h] <;> norm_num
  have hsx2 : sx * sx = 1 := by rcases hsx with h | h <;> rw [h] <;> norm_num
  have hsxy : sx * sy = 1 ∨ sx * sy = -1 := by
    rcases hsx with h | h <;> rcases hsy with h' | h' <;> rw [h, h'] <;> norm_num
  have hz : (2:ℚ) ^ j ≠ 0 := (two_zpow_pos j).ne'
  have hzi : (2:ℚ) ^ i ≠ 0 := (two_zpow_pos i).ne'
  have hsy0 : sy ≠ 0 := by rcases hsy with h | h <;> rw [h] <;> norm_num
  have hden : sy * Y * 2 ^ j ≠ 0 := mul_ne_zero (mul_ne_zero hsy0 hY) hz
  have hinv : 1 / (sy * Y * 2 ^ j) = sy * (1 / Y) * 2 ^ (-j) := by
    rw [zpow_neg, div_eq_iff hden]
    rw [show sy * (1 / Y) * (2 ^ j)⁻¹ * (sy * Y * 2 ^ j)
        = (sy * sy) * ((1 / Y) * Y) * ((2 ^ j)⁻¹ * 2 ^ j) by ring, hsy2, one_div,
      inv_mul_cancel₀ hY, inv_mul_cancel₀ hz]
    ring
  have hzh : zhU p (sy * Y * 2 ^ j) = sy * zhU p Y * 2 ^ (-j) := by
    unfold zhU; rw [hinv, rneU_smul p hsy]
  have hzl : zlU p (sy * Y * 2 ^ j) = sy * zlU p Y * 2 ^ (-j) := by
    unfold zlU
    rw [hzh, hinv, show sy * (1 / Y) * 2 ^ (-j) - sy * zhU p Y * 2 ^ (-j)
      = sy * (1 / Y - zhU p Y) * 2 ^ (-j) by ring, rneU_smul p hsy]
  have hij : (2:ℚ) ^ i * 2 ^ (-j) = 2 ^ (i - j) := by rw [← zpow_split]; ring_nf
  constructor
  · unfold kernelU
    rw [hzh, hzl]
    have e1 : sx * X * 2 ^ i * (sy * zlU p Y * 2 ^ (-j)) = (sx * sy) * (X * zlU p Y) * 2 ^ (i - j) := by
      rw [← hij]; ring
    rw [e1, rneU_smul p hsxy]
    have e2 : sx * X * 2 ^ i * (sy * zhU p Y * 2 ^ (-j)) + sx * sy * rneU p (X * zlU p Y) * 2 ^ (i - j)
        = (sx * sy) * (X * zhU p Y + rneU p (X * zlU p Y)) * 2 ^ (i - j) := by
      rw [← hij]; ring
    rw [e2, rneU_smul p hsxy]
  · have e3 : sx * X * 2 ^ i / (sy * Y * 2 ^ j) = (sx * sy) * (X / Y) * 2 ^ (i - j) := by
      rw [← hij, zpow_neg, div_eq_iff hden]
      rw [show sx * sy * (X / Y) * (2 ^ i * (2 ^ j)⁻¹) * (sy * Y * 2 ^ j)
          = sx * (sy * sy) * X * (Y⁻¹ * Y) * 2 ^ i * ((2 ^ j)⁻¹ * 2 ^ j) by
            rw [div_eq_mul_inv]; ring, hsy2, inv_mul_cancel₀ hY, inv_mul_cancel₀ hz]
      ring
    rw [e3, rneU_smul p hsxy]

/-- **Soundness of the check** (unbounded exponent, round-to-nearest-even). -/
theorem accept_sound {p : ℕ} (hp : 2 ≤ p) (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hacc : accept p Y = true) {x y : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j)) :
    kernelU p x y = rneU p (x / y) := by
  have hp1 : 1 ≤ p := by omega
  by_cases hadm : Admissible p X Y
  · exact alg2_float hp X Y i j hX1 hX2 hY1 hY2 hadm hx hy (rneU_nearest hp1 _)
      (rneU_nearest hp1 _) (rneU_nearest hp1 _) (rneU_nearest hp1 _) (rneU_nearest hp1 _)
  · obtain ⟨hYodd, hcand⟩ := inadmissible_is_cand hp hX1 hY1 hadm
    have hXY : X < Y := by
      unfold Admissible at hadm; push Not at hadm; exact hadm.1
    -- the check evaluated the kernel at X
    have hok : okAt p X Y = true := by
      unfold accept at hacc
      have hne : decide (Y % 2 = 0) = false := by simp; omega
      rw [hne, Bool.false_or, Bool.and_eq_true] at hacc
      rcases hcand with h | h <;> rw [h]
      · exact hacc.1
      · exact hacc.2
    unfold okAt at hok
    have hin : (decide ((2:ℤ) ^ p ≤ 2 * X) && decide (X < Y)) = true := by simp; omega
    rw [hin] at hok
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hok
    -- transfer by signs and powers of two
    have hYq : (Y:ℚ) ≠ 0 := by
      have : (0:ℤ) < Y := by
        have : (0:ℤ) < 2 ^ p := by positivity
        omega
      exact_mod_cast this.ne'
    obtain ⟨sx, hsx, hxe⟩ : ∃ sx : ℚ, (sx = 1 ∨ sx = -1) ∧ x = sx * X * 2 ^ i := by
      rcases hx with h | h
      · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
      · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
    obtain ⟨sy, hsy, hye⟩ : ∃ sy : ℚ, (sy = 1 ∨ sy = -1) ∧ y = sy * Y * 2 ^ j := by
      rcases hy with h | h
      · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
      · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
    obtain ⟨h1, h2⟩ := kernelU_smul p hsx hsy (X:ℚ) (Y:ℚ) hYq i j
    rw [hxe, hye, h1, h2, hok]

end ExactFDiv
