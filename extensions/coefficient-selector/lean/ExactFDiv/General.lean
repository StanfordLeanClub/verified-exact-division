/-
Exact division by an invariant floating-point divisor — Theorem A for arbitrary nonzero floats
`x = ± X * 2^i`, `y = ± Y * 2^j` (unbounded exponent), and the even-significand corollary.
-/
import ExactFDiv.Main

namespace ExactFDiv

/-- The hypothesis of Theorem A on a pair of integer significands. -/
def Admissible (p : ℕ) (X Y : ℤ) : Prop :=
  Y ≤ X ∨ ∀ B : ℤ, X * 2 ^ (p + 1) - B * Y ≠ 1 ∧ X * 2 ^ (p + 1) - B * Y ≠ -1

/-- An even divisor significand is admissible for every dividend significand. -/
theorem admissible_of_even {p : ℕ} (X Y : ℤ) (hY : 2 ∣ Y) : Admissible p X Y := by
  right
  intro B
  obtain ⟨c, rfl⟩ := hY
  have h2 : X * 2 ^ (p + 1) - B * (2 * c) = 2 * (X * 2 ^ p - B * c) := by ring
  rw [h2]
  constructor <;> omega

/-- Theorem A for positive floats with arbitrary exponents. -/
theorem alg2_pos {p : ℕ} (hp : 2 ≤ p) (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hcand : Admissible p X Y)
    {x y zh zl t1 q2 q : ℚ}
    (hx : x = X * (2:ℚ) ^ i) (hy : y = Y * (2:ℚ) ^ j)
    (hzh : IsNearest p (1 / y) zh)
    (hzl : IsNearest p (1 / y - zh) zl)
    (ht1 : IsNearest p (x * zl) t1)
    (hq2 : IsNearest p (x * zh + t1) q2)
    (hq : IsNearest p (x / y) q) : q2 = q := by
  have hY0 : (0:ℚ) < (Y:ℚ) := by
    have h0 : (0:ℤ) < 2 ^ p := by positivity
    have : (0:ℤ) < Y := by linarith
    exact_mod_cast this
  have hA : (0:ℚ) < 2 ^ i := two_zpow_pos i
  have hB : (0:ℚ) < 2 ^ j := two_zpow_pos j
  have hsub : (2:ℚ) ^ (j - i) = 2 ^ j / 2 ^ i := zpow_sub₀ (by norm_num) j i
  have hC : (0:ℚ) < 2 ^ (j - i) := two_zpow_pos _
  have s1 := hzh.scale j
  have s2 := hzl.scale j
  have s3 := ht1.scale (j - i)
  have s4 := hq2.scale (j - i)
  have s5 := hq.scale (j - i)
  have r1 : 1 / y * 2 ^ j = 1 / (Y:ℚ) := by rw [hy]; field_simp
  have r2 : (1 / y - zh) * 2 ^ j = 1 / (Y:ℚ) - zh * 2 ^ j := by rw [sub_mul, r1]
  have r3 : x * zl * 2 ^ (j - i) = (X:ℚ) * (zl * 2 ^ j) := by rw [hsub, hx]; field_simp
  have r4 : (x * zh + t1) * 2 ^ (j - i) = (X:ℚ) * (zh * 2 ^ j) + t1 * 2 ^ (j - i) := by
    rw [add_mul]; congr 1; rw [hsub, hx]; field_simp
  have r5 : x / y * 2 ^ (j - i) = (X:ℚ) / (Y:ℚ) := by rw [hsub, hx, hy]; field_simp
  rw [r1] at s1
  rw [r2] at s2
  rw [r3] at s3
  rw [r4] at s4
  rw [r5] at s5
  have h := alg2_core hp X Y hX1 hX2 hY1 hY2 hcand s1 s2 s3 s4 s5
  exact mul_right_cancel₀ hC.ne' h

/-- Theorem A for arbitrary nonzero floats: signs `sx, sy ∈ {1, -1}`. -/
theorem alg2_float {p : ℕ} (hp : 2 ≤ p) (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p)
    (hcand : Admissible p X Y)
    {x y zh zl t1 q2 q : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : IsNearest p (1 / y) zh)
    (hzl : IsNearest p (1 / y - zh) zl)
    (ht1 : IsNearest p (x * zl) t1)
    (hq2 : IsNearest p (x * zh + t1) q2)
    (hq : IsNearest p (x / y) q) : q2 = q := by
  rcases hy with hy | hy
  · rcases hx with hx | hx
    · exact alg2_pos hp X Y i j hX1 hX2 hY1 hY2 hcand hx hy hzh hzl ht1 hq2 hq
    · -- x negative: negate t1, q2, q
      have hx' : -x = X * (2:ℚ) ^ i := by rw [hx]; ring
      have n3 := ht1.neg
      have n4 := hq2.neg
      have n5 := hq.neg
      have r3 : -(x * zl) = -x * zl := by ring
      have r4 : -(x * zh + t1) = -x * zh + -t1 := by ring
      have r5 : -(x / y) = -x / y := by ring
      rw [r3] at n3
      rw [r4] at n4
      rw [r5] at n5
      have h := alg2_pos hp X Y i j hX1 hX2 hY1 hY2 hcand hx' hy hzh hzl n3 n4 n5
      exact neg_injective h
  · have hy' : -y = Y * (2:ℚ) ^ j := by rw [hy]; ring
    have m1 := hzh.neg
    have m2 := hzl.neg
    have q1 : -(1 / y) = 1 / -y := by rw [one_div, one_div, inv_neg]
    have q2' : -(1 / y - zh) = 1 / -y - -zh := by rw [← q1]; ring
    rw [q1] at m1
    rw [q2'] at m2
    rcases hx with hx | hx
    · -- y negative, x positive: negate zh, zl, t1, q2, q
      have n3 := ht1.neg
      have n4 := hq2.neg
      have n5 := hq.neg
      have r3 : -(x * zl) = x * -zl := by ring
      have r4 : -(x * zh + t1) = x * -zh + -t1 := by ring
      have r5 : -(x / y) = x / -y := by rw [div_neg]
      rw [r3] at n3
      rw [r4] at n4
      rw [r5] at n5
      have h := alg2_pos hp X Y i j hX1 hX2 hY1 hY2 hcand hx hy' m1 m2 n3 n4 n5
      exact neg_injective h
    · -- both negative: negate zh, zl only
      have hx' : -x = X * (2:ℚ) ^ i := by rw [hx]; ring
      have r3 : x * zl = -x * -zl := by ring
      have r4 : x * zh + t1 = -x * -zh + t1 := by ring
      have r5 : x / y = -x / -y := by rw [neg_div_neg_eq]
      rw [r3] at ht1
      rw [r4] at hq2
      rw [r5] at hq
      exact alg2_pos hp X Y i j hX1 hX2 hY1 hY2 hcand hx' hy' m1 m2 ht1 hq2 hq

/-- Corollary A1: if the divisor's significand is even, Algorithm 2 is correctly rounded for
every nonzero dividend. -/
theorem alg2_even {p : ℕ} (hp : 2 ≤ p) (X Y i j : ℤ)
    (hX1 : (2:ℤ) ^ p ≤ 2 * X) (hX2 : X < 2 ^ p)
    (hY1 : (2:ℤ) ^ p ≤ 2 * Y) (hY2 : Y < 2 ^ p) (hYeven : 2 ∣ Y)
    {x y zh zl t1 q2 q : ℚ}
    (hx : x = X * (2:ℚ) ^ i ∨ x = -(X * (2:ℚ) ^ i))
    (hy : y = Y * (2:ℚ) ^ j ∨ y = -(Y * (2:ℚ) ^ j))
    (hzh : IsNearest p (1 / y) zh)
    (hzl : IsNearest p (1 / y - zh) zl)
    (ht1 : IsNearest p (x * zl) t1)
    (hq2 : IsNearest p (x * zh + t1) q2)
    (hq : IsNearest p (x / y) q) : q2 = q :=
  alg2_float hp X Y i j hX1 hX2 hY1 hY2 (admissible_of_even X Y hYeven) hx hy hzh hzl ht1 hq2 hq

/-- Corollary A2 (uniqueness of the candidate): for an odd divisor significand `Y` and a fixed
sign `s`, at most one `X` in `[0, Y)` satisfies `X * 2^(p+1) = B * Y + s` for some `B`. -/
theorem candidate_unique {p : ℕ} {Y X₁ X₂ B₁ B₂ s : ℤ} (hYodd : ¬ 2 ∣ Y) (hY0 : 0 < Y)
    (h1a : 0 ≤ X₁) (h1b : X₁ < Y) (h2a : 0 ≤ X₂) (h2b : X₂ < Y)
    (e1 : X₁ * 2 ^ (p + 1) - B₁ * Y = s) (e2 : X₂ * 2 ^ (p + 1) - B₂ * Y = s) : X₁ = X₂ := by
  have hd : Y ∣ (X₁ - X₂) * 2 ^ (p + 1) := ⟨B₁ - B₂, by linear_combination e1 - e2⟩
  have hodd : IsCoprime Y (2:ℤ) := by
    refine ⟨1, -(Y / 2), ?_⟩
    omega
  have hcop : IsCoprime Y ((2:ℤ) ^ (p + 1)) := hodd.pow_right
  have hdvd : Y ∣ X₁ - X₂ := hcop.dvd_of_dvd_mul_right hd
  obtain ⟨c, hc⟩ := hdvd
  have hlt1 : X₁ - X₂ < Y := by linarith
  have hlt2 : -Y < X₁ - X₂ := by linarith
  have hc0 : c = 0 := by
    rw [hc] at hlt1 hlt2
    have h3 : c < 1 := by
      by_contra h; push Not at h
      have := mul_le_mul_of_nonneg_left h hY0.le
      linarith
    have h4 : -1 < c := by
      by_contra h; push Not at h
      have := mul_le_mul_of_nonneg_left h hY0.le
      linarith
    omega
  rw [hc0, mul_zero] at hc
  linarith

/-- Corollary A2, continued: the candidate for sign `+1` and the candidate for sign `-1` sum to
`Y`. -/
theorem candidates_sum {p : ℕ} {Y X₁ X₂ B₁ B₂ : ℤ} (hYodd : ¬ 2 ∣ Y) (hY0 : 0 < Y)
    (h1a : 0 < X₁) (h1b : X₁ < Y) (h2a : 0 < X₂) (h2b : X₂ < Y)
    (e1 : X₁ * 2 ^ (p + 1) - B₁ * Y = 1) (e2 : X₂ * 2 ^ (p + 1) - B₂ * Y = -1) :
    X₁ + X₂ = Y := by
  have hd : Y ∣ (X₁ + X₂) * 2 ^ (p + 1) := ⟨B₁ + B₂, by linear_combination e1 + e2⟩
  have hodd : IsCoprime Y (2:ℤ) := by
    refine ⟨1, -(Y / 2), ?_⟩
    omega
  have hcop : IsCoprime Y ((2:ℤ) ^ (p + 1)) := hodd.pow_right
  have hdvd : Y ∣ X₁ + X₂ := hcop.dvd_of_dvd_mul_right hd
  obtain ⟨c, hc⟩ := hdvd
  have h3 : c < 2 := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hY0.le
    linarith
  have h4 : 0 < c := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hY0.le
    linarith
  have hc1 : c = 1 := by omega
  rw [hc, hc1, mul_one]

/-- Hence at most one of the two candidates is a normalised significand (`≥ 2^(p-1)`): the
per-divisor check needs a single evaluation. -/
theorem candidates_not_both {p : ℕ} {Y X₁ X₂ B₁ B₂ : ℤ} (hYodd : ¬ 2 ∣ Y) (hY0 : 0 < Y)
    (hY2 : Y < 2 ^ p)
    (g1 : (2:ℤ) ^ p ≤ 2 * X₁) (h1b : X₁ < Y) (g2 : (2:ℤ) ^ p ≤ 2 * X₂) (h2b : X₂ < Y)
    (e1 : X₁ * 2 ^ (p + 1) - B₁ * Y = 1) (e2 : X₂ * 2 ^ (p + 1) - B₂ * Y = -1) : False := by
  have hpos : (0:ℤ) < 2 ^ p := by positivity
  have hs := candidates_sum hYodd hY0 (by linarith) h1b (by linarith) h2b e1 e2
  linarith

end ExactFDiv
