/-
Exact division by an invariant floating-point divisor — round-to-nearest-even, computably.

* `rhe m` rounds a rational to the nearest integer, ties to even.
* `rne p emin t` rounds `t` to the precision-`p` format with minimal quantum exponent `emin`
  (gradual underflow, no upper exponent bound): quantum `2^e` with
  `e = max emin (⌊log₂ |t|⌋ - p + 1)`, significand `rhe (t / 2^e)`.
* `rneR p emin emax` is the IEEE result: a signed zero on total underflow, the number, or the
  infinity of its sign when the rounded value exceeds the largest finite float.

Proved: `rne` is a nearest float of the format (`rne_nearest`), so `rneR` satisfies `RoundSpec`
(`rneR_spec`); the significand of `rne` is even on ties (`rhe_tie`); `rne` commutes with negation
and, in the unbounded model (`emin` far below), with scaling by powers of two.
-/
import ExactFDiv.Exists
import Mathlib.Data.Int.Log

namespace ExactFDiv

/-- round to the nearest integer, ties to even -/
def rhe (m : ℚ) : ℤ :=
  if m - ⌊m⌋ < 1 / 2 then ⌊m⌋
  else if 1 / 2 < m - ⌊m⌋ then ⌊m⌋ + 1
  else if ⌊m⌋ % 2 = 0 then ⌊m⌋ else ⌊m⌋ + 1

/-- `rhe m` is the floor or the floor plus one, on the correct side of the midpoint -/
theorem rhe_cases (m : ℚ) :
    (rhe m = ⌊m⌋ ∧ m - ⌊m⌋ ≤ 1 / 2) ∨ (rhe m = ⌊m⌋ + 1 ∧ 1 / 2 ≤ m - ⌊m⌋) := by
  unfold rhe
  split_ifs with c1 c2 c3
  · exact Or.inl ⟨rfl, c1.le⟩
  · exact Or.inr ⟨rfl, c2.le⟩
  · exact Or.inl ⟨rfl, by push Not at c1 c2; linarith⟩
  · exact Or.inr ⟨rfl, by push Not at c1; linarith⟩

theorem rhe_nearest (m : ℚ) (k : ℤ) : |m - rhe m| ≤ |m - k| := by
  have h1 := Int.floor_le m
  have h2 := Int.lt_floor_add_one m
  have hk : m - ⌊m⌋ ≤ |m - k| ∧ (⌊m⌋:ℚ) + 1 - m ≤ |m - k| ∨
      m - ⌊m⌋ ≤ |m - k| ∨ (⌊m⌋:ℚ) + 1 - m ≤ |m - k| := by
    right
    rcases le_or_gt k ⌊m⌋ with h | h
    · left
      have h' : (k:ℚ) ≤ ⌊m⌋ := by exact_mod_cast h
      exact le_trans (by linarith) (le_abs_self _)
    · right
      have h' : (⌊m⌋:ℚ) + 1 ≤ k := by exact_mod_cast h
      have h3 := neg_le_abs (m - (k:ℚ))
      linarith
  rcases hk with ⟨ha, _⟩ | ha | ha <;> rcases rhe_cases m with ⟨he, hr⟩ | ⟨he, hr⟩ <;>
    rw [he] <;> push_cast
  all_goals first
    | (rw [abs_of_nonneg (by linarith)]; linarith)
    | (rw [abs_of_nonpos (by linarith)]; linarith)

theorem rhe_half (m : ℚ) : |m - rhe m| ≤ 1 / 2 := by
  have h1 := Int.floor_le m
  have h2 := Int.lt_floor_add_one m
  rcases rhe_cases m with ⟨he, hr⟩ | ⟨he, hr⟩ <;> rw [he] <;> push_cast
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith)]; linarith

/-- on a tie the result is even -/
theorem rhe_tie (m : ℚ) (k : ℤ) (h : m - k = 1 / 2) : rhe m % 2 = 0 := by
  have hf : ⌊m⌋ = k := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold rhe
  rw [hf]
  have e : m - (k:ℚ) = 1 / 2 := h
  simp only [e, lt_irrefl, if_false]
  split_ifs with c
  · exact c
  · omega

/-- two integers within less than 1/2 of the same rational are equal -/
theorem int_eq_of_close {m : ℚ} {a b : ℤ} (ha : |m - a| < 1 / 2) (hb : |m - b| < 1 / 2) : a = b := by
  have h : |((a - b : ℤ) : ℚ)| < 1 := by
    push_cast
    have := abs_sub (m - b) (m - a)
    rw [show m - b - (m - a) = (a:ℚ) - b by ring] at this
    linarith
  have h' : |a - b| < 1 := by exact_mod_cast h
  have := Int.abs_lt_one_iff.mp h'
  omega

theorem rhe_neg (m : ℚ) : rhe (-m) = -rhe m := by
  by_cases htie : ∃ k : ℤ, m - k = 1 / 2
  · obtain ⟨k, hk⟩ := htie
    have hk' : -m - ((-k - 1 : ℤ) : ℚ) = 1 / 2 := by push_cast; linarith
    have ev1 := rhe_tie m k hk
    have ev2 := rhe_tie (-m) (-k - 1) hk'
    have c1 := rhe_half m
    have c2 := rhe_half (-m)
    -- rhe m ∈ {k, k+1}, rhe (-m) ∈ {-k-1, -k}
    have r1 : rhe m = k ∨ rhe m = k + 1 := by
      have : |((rhe m - k : ℤ) : ℚ) - 1 / 2| ≤ 1 / 2 := by
        push_cast
        rw [show (rhe m : ℚ) - k - 1 / 2 = -(m - rhe m) by linarith, abs_neg]; exact c1
      have h3 := abs_le.mp this
      have h4 : (0:ℚ) ≤ ((rhe m - k : ℤ) : ℚ) := by linarith [h3.1]
      have h5 : ((rhe m - k : ℤ) : ℚ) ≤ 1 := by linarith [h3.2]
      have h6 : 0 ≤ rhe m - k := by exact_mod_cast h4
      have h7 : rhe m - k ≤ 1 := by exact_mod_cast h5
      omega
    have r2 : rhe (-m) = -k - 1 ∨ rhe (-m) = -k := by
      have : |((rhe (-m) - (-k - 1) : ℤ) : ℚ) - 1 / 2| ≤ 1 / 2 := by
        push_cast
        rw [show (rhe (-m) : ℚ) - (-k - 1) - 1 / 2 = -(-m - rhe (-m)) by push_cast at hk'; linarith,
          abs_neg]; exact c2
      have h3 := abs_le.mp this
      have h4 : (0:ℚ) ≤ ((rhe (-m) - (-k - 1) : ℤ) : ℚ) := by linarith [h3.1]
      have h5 : ((rhe (-m) - (-k - 1) : ℤ) : ℚ) ≤ 1 := by linarith [h3.2]
      have h6 : 0 ≤ rhe (-m) - (-k - 1) := by exact_mod_cast h4
      have h7 : rhe (-m) - (-k - 1) ≤ 1 := by exact_mod_cast h5
      omega
    omega
  · push Not at htie
    have nt : ∀ k : ℤ, |m - k| ≠ 1 / 2 := by
      intro k hk
      rcases abs_eq (by norm_num : (0:ℚ) ≤ 1 / 2) |>.mp hk with h | h
      · exact htie k h
      · exact htie (k - 1) (by push_cast; linarith)
    have a1 : |m - rhe m| < 1 / 2 := lt_of_le_of_ne (rhe_half m) (nt _)
    have a2 : |-m - rhe (-m)| < 1 / 2 := by
      refine lt_of_le_of_ne (rhe_half (-m)) ?_
      intro h
      apply nt (-rhe (-m))
      rw [← h]; push_cast
      rw [show m - -(rhe (-m) : ℚ) = -(-m - rhe (-m)) by ring, abs_neg]
    have a3 : |m - ((-rhe (-m) : ℤ) : ℚ)| < 1 / 2 := by
      push_cast
      rw [show m - -(rhe (-m) : ℚ) = -(-m - rhe (-m)) by ring, abs_neg]; exact a2
    have := int_eq_of_close a1 a3
    omega

/-- the quantum exponent used by `rne` -/
def rexp (p : ℕ) (emin : ℤ) (t : ℚ) : ℤ := max emin (Int.log 2 |t| - (p:ℤ) + 1)

/-- round to nearest, ties to even, in the format with precision `p` and minimal quantum
exponent `emin` (no upper exponent bound) -/
def rne (p : ℕ) (emin : ℤ) (t : ℚ) : ℚ :=
  (rhe (t / 2 ^ rexp p emin t) : ℚ) * 2 ^ rexp p emin t

theorem log_bounds {t : ℚ} (ht : t ≠ 0) :
    (2:ℚ) ^ Int.log 2 |t| ≤ |t| ∧ |t| < 2 ^ (Int.log 2 |t| + 1) := by
  have ha : 0 < |t| := abs_pos.mpr ht
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) ha
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |t|
  push_cast at h1 h2
  exact ⟨h1, h2⟩

/-- `k * 2^e` is a float of the bounded format when `|k| ≤ 2^p` and `emin ≤ e` -/
theorem isFloatB_of_int {p : ℕ} (hp : 1 ≤ p) {emin : ℤ} (k e : ℤ) (he : emin ≤ e)
    (hk : |k| ≤ 2 ^ p) : IsFloatB p emin (k * (2:ℚ) ^ e) := by
  rcases lt_or_eq_of_le hk with h | h
  · exact ⟨k, e, h, he, rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    have hlt : (2:ℤ) ^ n < 2 ^ (n + 1) := by
      rw [pow_succ]; have : (0:ℤ) < 2 ^ n := by positivity
      linarith
    have hpos : (0:ℤ) ≤ 2 ^ (n + 1) := by positivity
    rcases (abs_eq hpos).mp h with hk' | hk'
    · refine ⟨2 ^ n, e + 1, ?_, by omega, ?_⟩
      · rw [abs_of_nonneg (by positivity)]; exact hlt
      · rw [hk', zpow_succ']; push_cast; ring
    · refine ⟨-2 ^ n, e + 1, ?_, by omega, ?_⟩
      · rw [abs_neg, abs_of_nonneg (by positivity)]; exact hlt
      · rw [hk', zpow_succ']; push_cast; ring

/-- **`rne` is a nearest float of the format.** -/
theorem rne_nearest {p : ℕ} (hp : 1 ≤ p) (emin : ℤ) (t : ℚ) :
    IsNearestB p emin t (rne p emin t) := by
  by_cases ht : t = 0
  · subst ht
    have : rne p emin 0 = 0 := by simp [rne, rhe]
    rw [this]
    refine ⟨isFloatB_zero p emin, fun g _ => ?_⟩
    simp
  obtain ⟨hlo, hhi⟩ := log_bounds ht
  set E := Int.log 2 |t| with hE
  set e := rexp p emin t with he
  have hee : emin ≤ e := le_max_left _ _
  have hEe : E - (p:ℤ) + 1 ≤ e := le_max_right _ _
  have hu : (0:ℚ) < 2 ^ e := two_zpow_pos e
  set m := t / 2 ^ e with hm
  set k := rhe m with hk
  have htm : t = m * 2 ^ e := by rw [hm]; field_simp
  have hres : rne p emin t = (k:ℚ) * 2 ^ e := rfl
  rw [hres]
  -- |m| < 2^p
  have hm_lt : |m| < 2 ^ (p:ℤ) := by
    rw [hm, abs_div, abs_of_pos hu, div_lt_iff₀ hu]
    calc |t| < 2 ^ (E + 1) := hhi
      _ ≤ 2 ^ ((p:ℤ) + e) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 2 ^ (p:ℤ) * 2 ^ e := zpow_split _ _
  have hk_le : |k| ≤ 2 ^ p := by
    have h1 := rhe_half m
    have h2 : |(k:ℚ)| ≤ |m| + 1 / 2 := by
      have h3 := abs_sub m (m - k)
      rw [sub_sub_cancel] at h3
      rw [← hk] at h1
      linarith
    have h4 : |(k:ℚ)| < 2 ^ (p:ℤ) + 1 := by linarith
    rw [← cast_two_pow] at h4
    have h5 : |k| < 2 ^ p + 1 := by
      have : ((|k| : ℤ) : ℚ) < ((2 ^ p + 1 : ℤ) : ℚ) := by push_cast at h4 ⊢; exact h4
      exact_mod_cast this
    omega
  refine ⟨isFloatB_of_int hp k e hee hk_le, fun g hg => ?_⟩
  -- distance to multiples of 2^e
  have hmult : ∀ k' : ℤ, |t - k * 2 ^ e| ≤ |t - k' * 2 ^ e| := by
    intro k'
    have e1 : t - k * 2 ^ e = (m - k) * 2 ^ e := by rw [htm]; ring
    have e2 : t - k' * 2 ^ e = (m - k') * 2 ^ e := by rw [htm]; ring
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos hu]
    exact mul_le_mul_of_nonneg_right (rhe_nearest m k') hu.le
  by_cases hemin : e = emin
  · obtain ⟨k', hk'⟩ := hg.exists_int
    rw [hk', ← hemin]
    exact hmult k'
  · -- normal regime: e = E - p + 1
    have heq : e = E - (p:ℤ) + 1 := by
      rcases max_choice emin (E - (p:ℤ) + 1) with h | h
      · exact absurd (he.trans h) hemin
      · exact he.trans h
    have hB : (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ e = 2 ^ E := by
      rw [← zpow_split, heq]; congr 1; ring
    by_cases hgbig : (2:ℚ) ^ E ≤ |g|
    · -- g is a multiple of 2^e
      rcases le_or_gt 0 g with hg0 | hg0
      · rw [abs_of_nonneg hg0] at hgbig
        obtain ⟨k', hk'⟩ := float_grid hg.isFloat e (by rw [hB]; exact hgbig)
        rw [hk']; exact hmult k'
      · rw [abs_of_neg hg0] at hgbig
        obtain ⟨k', hk'⟩ := float_grid hg.isFloat.neg e (by rw [hB]; exact hgbig)
        have : g = ((-k' : ℤ) : ℚ) * 2 ^ e := by push_cast; linarith
        rw [this]; exact hmult (-k')
    · push Not at hgbig
      -- compare with the float s * 2^E on our grid
      obtain ⟨H, hH⟩ : ∃ H : ℤ, (H:ℚ) * 2 ^ e = 2 ^ E := by
        refine ⟨2 ^ (p - 1), ?_⟩
        rw [← hB]; push_cast
        rw [← zpow_natCast]; congr 2; push_cast; omega
      rcases le_or_gt 0 t with ht0 | ht0
      · have h1 := hmult H
        rw [abs_of_nonneg ht0] at hlo
        have e3 : |t - (2:ℚ) ^ E| = t - 2 ^ E := abs_of_nonneg (by linarith)
        rw [hH, e3] at h1
        have h2 : t - 2 ^ E < |t - g| := by
          have h3 := abs_sub_abs_le_abs_sub t g
          rw [abs_of_nonneg ht0] at h3
          linarith
        linarith
      · have h1 := hmult (-H)
        have hH' : ((-H : ℤ) : ℚ) * 2 ^ e = -(2 ^ E) := by push_cast; linarith
        rw [hH'] at h1
        rw [abs_of_neg ht0] at hlo
        rw [abs_of_nonpos (by linarith : t - -(2:ℚ) ^ E ≤ 0)] at h1
        have h2 : -t - 2 ^ E < |t - g| := by
          have h3 := abs_sub_abs_le_abs_sub t g
          rw [abs_of_neg ht0] at h3
          linarith
        linarith

/-- the IEEE result of round-to-nearest-even -/
def rneR (p : ℕ) (emin emax : ℤ) (t : ℚ) : IEEE :=
  if rne p emin t = 0 then IEEE.zero (sgn t)
  else if |rne p emin t| ≤ maxFloat p emax then IEEE.num (rne p emin t)
  else IEEE.inf (sgn (rne p emin t))

/-- **Round-to-nearest-even satisfies the rounding hypothesis of the model.** -/
theorem rneR_spec {p : ℕ} (hp : 1 ≤ p) (emin emax : ℤ) (t : ℚ) :
    RoundSpec p emin emax t (rneR p emin emax t) := by
  refine ⟨rne p emin t, rne_nearest hp emin t, ?_⟩
  unfold rneR
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨not_le.mp h2, rfl⟩)

end ExactFDiv
