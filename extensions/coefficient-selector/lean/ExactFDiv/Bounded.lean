/-
Exact division by an invariant floating-point divisor — formats with a minimal exponent
(gradual underflow).

`IsFloatB p emin` adds the constraint `emin ≤ e` (so subnormals are the floats with `e = emin`
and `|m| < 2^(p-1)`); rounding in such a format is `IsNearestB`.  The bridge lemma
`IsNearestB.toNearest` says that for a real of magnitude at least the smallest normal number
(or equal to zero) a nearest float of the bounded format is a nearest float of the unbounded
one.  `alg2_bounded` is then Theorem A for a format with subnormals, under the explicit
hypothesis that none of the five rounded quantities lies in the subnormal range.

Overflow is not modelled here: an IEEE operation returns the value below unless it exceeds the
largest finite float, in which case both sides of the conclusion become the same infinity.
-/
import ExactFDiv.General

namespace ExactFDiv

/-- floats of a format with minimal exponent `emin` (no upper bound on the exponent) -/
def IsFloatB (p : ℕ) (emin : ℤ) (f : ℚ) : Prop :=
  ∃ m e : ℤ, |m| < 2 ^ p ∧ emin ≤ e ∧ f = m * (2:ℚ) ^ e

/-- `f` is a float of the bounded format nearest to `t` (any tie-breaking rule) -/
def IsNearestB (p : ℕ) (emin : ℤ) (t f : ℚ) : Prop :=
  IsFloatB p emin f ∧ ∀ g, IsFloatB p emin g → |t - f| ≤ |t - g|

theorem IsFloatB.isFloat {p : ℕ} {emin : ℤ} {f : ℚ} (h : IsFloatB p emin f) : IsFloat p f := by
  obtain ⟨m, e, hm, _, rfl⟩ := h
  exact ⟨m, e, hm, rfl⟩

theorem IsFloatB.neg {p : ℕ} {emin : ℤ} {f : ℚ} (h : IsFloatB p emin f) :
    IsFloatB p emin (-f) := by
  obtain ⟨m, e, hm, he, rfl⟩ := h
  exact ⟨-m, e, by rwa [abs_neg], he, by push_cast; ring⟩

/-- the smallest positive normal number `2^(p-1) * 2^emin` -/
def minNormal (p : ℕ) (emin : ℤ) : ℚ := 2 ^ ((p:ℤ) - 1) * 2 ^ emin

theorem isFloatB_minNormal {p : ℕ} (hp : 1 ≤ p) (emin : ℤ) :
    IsFloatB p emin (minNormal p emin) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  refine ⟨2 ^ n, emin, ?_, le_refl _, ?_⟩
  · rw [abs_of_nonneg (by positivity), pow_succ]
    have : (0:ℤ) < 2 ^ n := by positivity
    linarith
  · unfold minNormal
    have e1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    rw [e1, ← cast_two_pow]

/-- **Bridge.** Away from the subnormal range, rounding in the bounded format is rounding in the
unbounded one. -/
theorem IsNearestB.toNearest {p : ℕ} (hp : 1 ≤ p) {emin : ℤ} {t f : ℚ}
    (h : IsNearestB p emin t f) (ht : minNormal p emin ≤ |t| ∨ t = 0) : IsNearest p t f := by
  refine ⟨h.1.isFloat, fun g hg => ?_⟩
  rcases ht with ht | ht
  · obtain ⟨m, e, hm, rfl⟩ := hg
    by_cases he : emin ≤ e
    · exact h.2 _ ⟨m, e, hm, he, rfl⟩
    · push Not at he
      have hlam := isFloatB_minNormal hp emin
      have hgl : |(m:ℚ) * 2 ^ e| < minNormal p emin := by
        have hm' : |(m:ℚ)| < 2 ^ (p:ℤ) := by
          rw [← cast_two_pow, ← Int.cast_abs]; exact_mod_cast hm
        have h1 : (2:ℚ) ^ e ≤ 2 ^ (emin - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        rw [abs_mul, abs_of_pos (two_zpow_pos e)]
        calc |(m:ℚ)| * 2 ^ e ≤ |(m:ℚ)| * 2 ^ (emin - 1) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ < 2 ^ (p:ℤ) * 2 ^ (emin - 1) := mul_lt_mul_of_pos_right hm' (two_zpow_pos _)
          _ = minNormal p emin := by
              unfold minNormal; rw [← zpow_split, ← zpow_split]; congr 1; ring
      have hg1 := abs_lt.mp hgl
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0] at ht
        have h1 := h.2 _ hlam
        rw [abs_of_nonneg (by linarith : 0 ≤ t - minNormal p emin)] at h1
        rw [abs_of_nonneg (by linarith [hg1.2] : 0 ≤ t - (m:ℚ) * 2 ^ e)]
        linarith [hg1.2]
      · rw [abs_of_neg h0] at ht
        have h1 := h.2 _ hlam.neg
        rw [abs_of_nonpos (by linarith : t - -(minNormal p emin) ≤ 0)] at h1
        rw [abs_of_nonpos (by linarith [hg1.1] : t - (m:ℚ) * 2 ^ e ≤ 0)]
        linarith [hg1.1]
  · subst ht
    have h0 : IsFloatB p emin 0 := ⟨0, emin, by rw [abs_zero]; positivity, le_refl _, by simp⟩
    have h1 := h.2 0 h0
    have hf : f = 0 := by
      have h2 : |0 - f| ≤ 0 := by simpa using h1
      have h3 : 0 - f = 0 := abs_nonpos_iff.mp h2
      linarith
    rw [hf]
    simp

/-- **Theorem A in a format with subnormals.** If none of the five rounded quantities is in the
subnormal range (the two correction terms may also be exactly zero), the kernel
`q2 = RN(x*zh + RN(x*zl))` returns the correctly rounded quotient. -/
theorem alg2_bounded {p : ℕ} (hp : 2 ≤ p) (emin : ℤ) (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hcand : Admissible p X Y)
    {x y zh zl t1 q2 q : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : IsNearestB p emin (1 / y) zh) (n1 : minNormal p emin ≤ |1 / y|)
    (hzl : IsNearestB p emin (1 / y - zh) zl)
    (n2 : minNormal p emin ≤ |1 / y - zh| ∨ 1 / y - zh = 0)
    (ht1 : IsNearestB p emin (x * zl) t1) (n3 : minNormal p emin ≤ |x * zl| ∨ x * zl = 0)
    (hq2 : IsNearestB p emin (x * zh + t1) q2) (n4 : minNormal p emin ≤ |x * zh + t1|)
    (hq : IsNearestB p emin (x / y) q) (n5 : minNormal p emin ≤ |x / y|) : q2 = q := by
  have hp1 : 1 ≤ p := by omega
  exact alg2_float hp X Y i j hX1 hX2 hY1 hY2 hcand hx hy
    (hzh.toNearest hp1 (Or.inl n1)) (hzl.toNearest hp1 n2) (ht1.toNearest hp1 n3)
    (hq2.toNearest hp1 (Or.inl n4)) (hq.toNearest hp1 (Or.inl n5))

end ExactFDiv
