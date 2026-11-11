/-
Exact division by an invariant floating-point divisor — basic theory of round-to-nearest
in radix 2, precision `p`, unbounded exponent range.

Everything is stated over `ℚ` and for an arbitrary round-to-nearest function (no tie-breaking
rule is assumed): `IsNearest p t f` says that `f` is a precision-`p` float at minimal distance
from `t`.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Round

namespace ExactFDiv

/-- `f` is a radix-2 floating-point number of precision `p` (unbounded exponent). -/
def IsFloat (p : ℕ) (f : ℚ) : Prop :=
  ∃ m e : ℤ, |m| < 2 ^ p ∧ f = m * (2:ℚ) ^ e

/-- `f` is a precision-`p` float nearest to `t` (any tie-breaking rule). -/
def IsNearest (p : ℕ) (t f : ℚ) : Prop :=
  IsFloat p f ∧ ∀ g, IsFloat p g → |t - f| ≤ |t - g|

theorem two_zpow_pos (e : ℤ) : (0:ℚ) < 2 ^ e := by positivity

theorem zpow_split (a b : ℤ) : (2:ℚ) ^ (a + b) = 2 ^ a * 2 ^ b :=
  zpow_add₀ (by norm_num) a b

theorem zpow_succ' (a : ℤ) : (2:ℚ) ^ (a + 1) = 2 ^ a * 2 := by
  rw [zpow_split]; norm_num

theorem zpow_pred' (a : ℤ) : (2:ℚ) ^ (a - 1) = 2 ^ a / 2 := by
  have h := zpow_succ' (a - 1)
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem IsFloat.neg {p : ℕ} {f : ℚ} (h : IsFloat p f) : IsFloat p (-f) := by
  obtain ⟨m, e, hm, rfl⟩ := h
  exact ⟨-m, e, by rwa [abs_neg], by push_cast; ring⟩

theorem IsFloat.scale {p : ℕ} {f : ℚ} (h : IsFloat p f) (k : ℤ) : IsFloat p (f * 2 ^ k) := by
  obtain ⟨m, e, hm, rfl⟩ := h
  exact ⟨m, e + k, hm, by rw [zpow_split]; ring⟩

theorem IsNearest.neg {p : ℕ} {t f : ℚ} (h : IsNearest p t f) : IsNearest p (-t) (-f) := by
  refine ⟨h.1.neg, fun g hg => ?_⟩
  have h1 := h.2 (-g) hg.neg
  have e1 : -t - -f = -(t - f) := by ring
  have e2 : -t - g = -(t - -g) := by ring
  rw [e1, e2, abs_neg, abs_neg]; exact h1

theorem IsNearest.scale {p : ℕ} {t f : ℚ} (h : IsNearest p t f) (k : ℤ) :
    IsNearest p (t * 2 ^ k) (f * 2 ^ k) := by
  refine ⟨h.1.scale k, fun g hg => ?_⟩
  have hk : (0:ℚ) < 2 ^ k := two_zpow_pos k
  have h1 := h.2 _ (hg.scale (-k))
  have hone : (2:ℚ) ^ (-k) * 2 ^ k = 1 := by rw [← zpow_split]; simp
  have e1 : t * 2 ^ k - f * 2 ^ k = (t - f) * 2 ^ k := by ring
  have e2 : t * 2 ^ k - g = (t - g * 2 ^ (-k)) * 2 ^ k := by linear_combination g * hone
  rw [e1, e2, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- A nearest float does not jump over a float: upper bound. -/
theorem IsNearest.le_of_le {p : ℕ} {t f B : ℚ} (h : IsNearest p t f) (hB : IsFloat p B)
    (hle : t ≤ B) : f ≤ B := by
  by_contra hf
  push Not at hf
  have h1 := h.2 B hB
  rw [abs_of_nonpos (by linarith : t - f ≤ 0), abs_of_nonpos (by linarith : t - B ≤ 0)] at h1
  linarith

/-- A nearest float does not jump over a float: lower bound. -/
theorem IsNearest.ge_of_ge {p : ℕ} {t f B : ℚ} (h : IsNearest p t f) (hB : IsFloat p B)
    (hle : B ≤ t) : B ≤ f := by
  by_contra hf
  push Not at hf
  have h1 := h.2 B hB
  rw [abs_of_nonneg (by linarith : 0 ≤ t - f), abs_of_nonneg (by linarith : 0 ≤ t - B)] at h1
  linarith

theorem cast_two_pow (p : ℕ) : ((2 ^ p : ℤ) : ℚ) = (2:ℚ) ^ (p:ℤ) := by
  push_cast; rw [zpow_natCast]

/-- `k * 2^e` is a float as soon as `|k| ≤ 2^p` (the endpoint `2^p` is a float with one more
exponent). -/
theorem isFloat_of_int {p : ℕ} (hp : 1 ≤ p) (k e : ℤ) (hk : |k| ≤ 2 ^ p) :
    IsFloat p (k * (2:ℚ) ^ e) := by
  rcases lt_or_eq_of_le hk with h | h
  · exact ⟨k, e, h, rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    have hlt : (2:ℤ) ^ n < 2 ^ (n + 1) := by
      rw [pow_succ]; have : (0:ℤ) < 2 ^ n := by positivity
      linarith
    have hpos : (0:ℤ) ≤ 2 ^ (n + 1) := by positivity
    rcases (abs_eq hpos).mp h with hk' | hk'
    · refine ⟨2 ^ n, e + 1, ?_, ?_⟩
      · rw [abs_of_nonneg (by positivity)]; exact hlt
      · rw [hk', zpow_succ']; push_cast; ring
    · refine ⟨-2 ^ n, e + 1, ?_, ?_⟩
      · rw [abs_neg, abs_of_nonneg (by positivity)]; exact hlt
      · rw [hk', zpow_succ']; push_cast; ring

/-- A float that is at least `2^(p-1) * 2^e` is an integer multiple of `2^e`. -/
theorem float_grid {p : ℕ} {g : ℚ} (hg : IsFloat p g) (e : ℤ)
    (hlo : (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ e ≤ g) : ∃ k : ℤ, g = k * (2:ℚ) ^ e := by
  obtain ⟨m, e', hm, rfl⟩ := hg
  have hpos : (0:ℚ) < 2 ^ ((p:ℤ) - 1) * 2 ^ e := by positivity
  have he' : (0:ℚ) < 2 ^ e' := two_zpow_pos e'
  have hm0 : (0:ℚ) < m := by
    by_contra h
    push Not at h
    have : (m:ℚ) * 2 ^ e' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h he'.le
    linarith
  have hm0' : 0 < m := by exact_mod_cast hm0
  have hmlt : (m:ℚ) < 2 ^ (p:ℤ) := by
    rw [abs_of_pos hm0'] at hm
    rw [← cast_two_pow]; exact_mod_cast hm
  have hee : e ≤ e' := by
    by_contra h
    push Not at h
    have h1 : (2:ℚ) ^ e' ≤ 2 ^ (e - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (m:ℚ) * 2 ^ e' < 2 ^ (p:ℤ) * 2 ^ (e - 1) := by
      calc (m:ℚ) * 2 ^ e' ≤ m * 2 ^ (e - 1) := mul_le_mul_of_nonneg_left h1 hm0.le
        _ < 2 ^ (p:ℤ) * 2 ^ (e - 1) := mul_lt_mul_of_pos_right hmlt (two_zpow_pos _)
    have h3 : (2:ℚ) ^ (p:ℤ) * 2 ^ (e - 1) = 2 ^ ((p:ℤ) - 1) * 2 ^ e := by
      rw [← zpow_split, ← zpow_split]; congr 1; ring
    linarith
  refine ⟨m * 2 ^ (e' - e).toNat, ?_⟩
  have h4 : (2:ℚ) ^ e' = 2 ^ (((e' - e).toNat : ℕ) : ℤ) * 2 ^ e := by
    rw [← zpow_split]; congr 1; rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [h4]; push_cast; rw [zpow_natCast]; ring

/-- Half-ulp error bound: if `|t| ≤ 2^p * 2^e` then a nearest float is within `2^e / 2`. -/
theorem IsNearest.err {p : ℕ} (hp : 1 ≤ p) {t f : ℚ} (h : IsNearest p t f) (e : ℤ)
    (ht : |t| ≤ 2 ^ (p:ℤ) * 2 ^ e) : |t - f| ≤ 2 ^ e / 2 := by
  have hu : (0:ℚ) < 2 ^ e := two_zpow_pos e
  set k : ℤ := round (t / 2 ^ e) with hk
  have h1 : |t / 2 ^ e - k| ≤ 1 / 2 := abs_sub_round _
  have hr : |t / 2 ^ e| ≤ (2:ℚ) ^ (p:ℤ) := by
    rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]; exact ht
  have hkb : |k| ≤ 2 ^ p := by
    rw [abs_le] at h1 hr
    have hk1 : (k:ℚ) < ((2 ^ p + 1 : ℤ) : ℚ) := by
      push_cast; rw [← zpow_natCast]; linarith [h1.1, hr.2]
    have hk2 : ((-(2 ^ p) - 1 : ℤ) : ℚ) < k := by
      push_cast; rw [← zpow_natCast]; linarith [h1.2, hr.1]
    have hk1' : k < 2 ^ p + 1 := by exact_mod_cast hk1
    have hk2' : -(2 ^ p) - 1 < k := by exact_mod_cast hk2
    rw [abs_le]; constructor <;> linarith
  have h2 := h.2 _ (isFloat_of_int hp k e hkb)
  have h3 : |t - k * 2 ^ e| ≤ 2 ^ e / 2 := by
    have e1 : t - k * 2 ^ e = (t / 2 ^ e - k) * 2 ^ e := by field_simp
    rw [e1, abs_mul, abs_of_pos hu]
    nlinarith [abs_nonneg (t / 2 ^ e - k)]
  linarith

/-- If `t` is strictly closer than half a grid step to the grid point `k * 2^e`
(`2^(p-1) ≤ k ≤ 2^p`), and not too far below it when `k = 2^(p-1)` is a binade boundary,
then every nearest float of `t` equals `k * 2^e`. -/
theorem nearest_unique {p : ℕ} (hp : 1 ≤ p) {t f : ℚ} (h : IsNearest p t f) (k e : ℤ)
    (hk1 : (2:ℚ) ^ ((p:ℤ) - 1) ≤ k) (hk2 : (k:ℚ) ≤ 2 ^ (p:ℤ))
    (hclose : |t - k * 2 ^ e| < 2 ^ e / 2)
    (hedge : (k:ℚ) = 2 ^ ((p:ℤ) - 1) → -(2 ^ e / 4) < t - k * 2 ^ e) :
    f = k * 2 ^ e := by
  have hu : (0:ℚ) < 2 ^ e := two_zpow_pos e
  have hkpos : (0:ℚ) < k := lt_of_lt_of_le (two_zpow_pos _) hk1
  have hkZ : |k| ≤ 2 ^ p := by
    have h0 : 0 < k := by exact_mod_cast hkpos
    rw [abs_of_pos h0]
    have : (k:ℚ) ≤ ((2 ^ p : ℤ) : ℚ) := by rw [cast_two_pow]; exact hk2
    exact_mod_cast this
  have hg0 : IsFloat p (k * (2:ℚ) ^ e) := isFloat_of_int hp k e hkZ
  have hf := h.2 _ hg0
  have hfk : |f - k * 2 ^ e| < 2 ^ e := by
    have : f - k * 2 ^ e = (t - k * 2 ^ e) - (t - f) := by ring
    rw [this]
    calc |(t - k * 2 ^ e) - (t - f)| ≤ |t - k * 2 ^ e| + |t - f| := abs_sub _ _
      _ < 2 ^ e := by linarith
  by_cases hfl : (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ e ≤ f
  · obtain ⟨k', hk'⟩ := float_grid h.1 e hfl
    have h1 : |((k' - k : ℤ) : ℚ)| < 1 := by
      have e1 : f - k * 2 ^ e = ((k' - k : ℤ) : ℚ) * 2 ^ e := by rw [hk']; push_cast; ring
      rw [e1, abs_mul, abs_of_pos hu] at hfk
      nlinarith [abs_nonneg ((k' - k : ℤ) : ℚ)]
    have h2 : |k' - k| < 1 := by exact_mod_cast h1
    have h3 : k' - k = 0 := Int.abs_lt_one_iff.mp h2
    have h4 : k' = k := by linarith
    rw [hk', h4]
  · exfalso
    push Not at hfl
    rw [abs_lt] at hfk
    rcases eq_or_lt_of_le hk1 with hkeq | hklt
    · -- k = 2^(p-1): binade boundary
      have hkeq' : (k:ℚ) = 2 ^ ((p:ℤ) - 1) := hkeq.symm
      have hed := hedge hkeq'
      rw [abs_lt] at hclose
      by_cases ht : 0 ≤ t - k * 2 ^ e
      · -- then f ≥ k * 2^e
        rw [abs_of_nonneg ht] at hf
        have := abs_le.mp hf
        rw [hkeq'] at this ht
        linarith [this.2]
      · push_neg at ht
        rw [abs_of_neg ht] at hf
        have hf' := abs_le.mp hf
        -- f > k u - u/2 = (2^p - 1) * 2^(e-1)
        have hlo : (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ (e - 1) ≤ f := by
          rw [zpow_pred' e]
          have hp1 : (1:ℚ) ≤ 2 ^ ((p:ℤ) - 1) := by
            have : (2:ℚ) ^ (0:ℤ) ≤ 2 ^ ((p:ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
            simpa using this
          rw [hkeq'] at hf' hed
          nlinarith [hf'.1, hf'.2]
        obtain ⟨k', hk'⟩ := float_grid h.1 (e - 1) hlo
        -- (2^p - 1) < k' < 2^p
        have hpp : (2:ℚ) ^ (p:ℤ) = 2 ^ ((p:ℤ) - 1) * 2 := by
          have := zpow_succ' ((p:ℤ) - 1); rw [sub_add_cancel] at this; exact this
        have hk'lt : (k':ℚ) < ((2 ^ p : ℤ) : ℚ) := by
          rw [cast_two_pow, hpp]
          rw [hk', zpow_pred' e] at hfl
          have : (k':ℚ) * (2 ^ e / 2) = (k' / 2) * 2 ^ e := by ring
          rw [this] at hfl
          have := lt_of_mul_lt_mul_right hfl hu.le
          linarith
        have hk'gt : ((2 ^ p - 1 : ℤ) : ℚ) < k' := by
          push_cast; rw [← zpow_natCast, hpp]
          rw [hkeq'] at hf' hed
          have hf1 : 2 ^ ((p:ℤ) - 1) * 2 ^ e - 2 ^ e / 2 < f := by linarith [hf'.1]
          rw [hk', zpow_pred' e] at hf1
          have e2 : (2:ℚ) ^ ((p:ℤ) - 1) * 2 ^ e - 2 ^ e / 2
              = ((2 ^ ((p:ℤ) - 1) * 2 - 1) / 2) * 2 ^ e := by ring
          have e3 : (k':ℚ) * (2 ^ e / 2) = (k' / 2) * 2 ^ e := by ring
          rw [e2, e3] at hf1
          have := lt_of_mul_lt_mul_right hf1 hu.le
          linarith
        have a1 : k' < 2 ^ p := by exact_mod_cast hk'lt
        have a2 : 2 ^ p - 1 < k' := by exact_mod_cast hk'gt
        linarith
    · -- k ≥ 2^(p-1) + 1 as integers, so f > k u - u ≥ 2^(p-1) u
      have hkint : (2:ℚ) ^ ((p:ℤ) - 1) + 1 ≤ k := by
        obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
        have e1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
        rw [e1] at hklt ⊢
        have : ((2 ^ n : ℤ) : ℚ) < k := by rw [cast_two_pow]; exact hklt
        have h1 : (2:ℤ) ^ n < k := by exact_mod_cast this
        have h2 : (2:ℤ) ^ n + 1 ≤ k := h1
        have : (((2:ℤ) ^ n + 1 : ℤ) : ℚ) ≤ k := by exact_mod_cast h2
        rw [← cast_two_pow]; push_cast at this ⊢; exact this
      nlinarith [hfk.1]

end ExactFDiv
