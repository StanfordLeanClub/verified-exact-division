/-
Exact division by an invariant floating-point divisor — a model of IEEE-754 arithmetic.

Data: NaN, signed infinities, signed zeros and nonzero finite numbers.  The operations `mul`,
`div` and `fma` follow the IEEE-754 rules for special operands in round-to-nearest; for finite
nonzero exact results they call a rounding function `R : ℚ → IEEE`, about which the theorems
assume only `RoundSpec`: `R t` is obtained from *some* nearest float of `t` in the format
(precision `p`, minimal exponent `emin`, gradual underflow), replaced by the infinity of its sign
if it exceeds the largest finite float.  Round-to-nearest-even is one such `R`.

Exception flags and NaN payloads are not modelled.

Exponent convention: `emin` and `emax` are *quantum* exponents (of the last significand bit), so the
finite floats are `m * 2^e` with `|m| < 2^p`, `emin ≤ e ≤ emax`.  For binary64 `p = 53`,
`emin = -1074`, `emax = 971` (not IEEE's -1022 / 1023); then `minNormal = DBL_MIN` and
`maxFloat = DBL_MAX`.  For binary32 `p = 24`, `emin = -149`, `emax = 104`.

`num v` is meant to carry a nonzero value; the theorems below that take `num` operands assume
nonzero values so that this junk case cannot be exploited.
-/
import ExactFDiv.Bounded

namespace ExactFDiv

/-- IEEE-754 data.  In `num v` the value `v` is meant to be nonzero. -/
inductive IEEE where
  | nan : IEEE
  | inf (neg : Bool) : IEEE
  | zero (neg : Bool) : IEEE
  | num (v : ℚ) : IEEE

/-- sign bit of a rational number -/
def sgn (v : ℚ) : Bool := decide (v < 0)

/-- the largest finite float `(2^p - 1) * 2^emax` -/
def maxFloat (p : ℕ) (emax : ℤ) : ℚ := (2 ^ (p:ℤ) - 1) * 2 ^ emax

/-- `r` is an admissible IEEE result for the nonzero exact value `t`: take a nearest float `f` of
the format with unbounded upper exponent; the result is a signed zero if `f = 0` (total
underflow), `f` itself if it is finite, and the infinity of the sign of `f` on overflow. -/
def RoundSpec (p : ℕ) (emin emax : ℤ) (t : ℚ) (r : IEEE) : Prop :=
  ∃ f, IsNearestB p emin t f ∧
    ((f = 0 ∧ r = IEEE.zero (sgn t)) ∨
     (f ≠ 0 ∧ |f| ≤ maxFloat p emax ∧ r = IEEE.num f) ∨
     (maxFloat p emax < |f| ∧ r = IEEE.inf (sgn f)))

/-- multiplication; `R` rounds a nonzero exact product -/
def mul (R : ℚ → IEEE) (a b : IEEE) : IEEE :=
  match a with
  | .nan => .nan
  | .inf s =>
    match b with
    | .nan => .nan
    | .inf s' => .inf (Bool.xor s s')
    | .zero _ => .nan
    | .num v => .inf (Bool.xor s (sgn v))
  | .zero s =>
    match b with
    | .nan => .nan
    | .inf _ => .nan
    | .zero s' => .zero (Bool.xor s s')
    | .num v => .zero (Bool.xor s (sgn v))
  | .num u =>
    match b with
    | .nan => .nan
    | .inf s => .inf (Bool.xor (sgn u) s)
    | .zero s => .zero (Bool.xor (sgn u) s)
    | .num v => R (u * v)

/-- division -/
def div (R : ℚ → IEEE) (a b : IEEE) : IEEE :=
  match a with
  | .nan => .nan
  | .inf s =>
    match b with
    | .nan => .nan
    | .inf _ => .nan
    | .zero s' => .inf (Bool.xor s s')
    | .num v => .inf (Bool.xor s (sgn v))
  | .zero s =>
    match b with
    | .nan => .nan
    | .inf s' => .zero (Bool.xor s s')
    | .zero _ => .nan
    | .num v => .zero (Bool.xor s (sgn v))
  | .num u =>
    match b with
    | .nan => .nan
    | .inf s => .zero (Bool.xor (sgn u) s)
    | .zero s => .inf (Bool.xor (sgn u) s)
    | .num v => R (u / v)

/-- fused multiply-add `a * b + c` with a single rounding (round-to-nearest sign rule for an
exact zero sum: `+0` unless both addends are zeros of the same sign). -/
def fma (R : ℚ → IEEE) (a b c : IEEE) : IEEE :=
  match mul IEEE.num a b with          -- the exact product
  | .nan => .nan
  | .inf s =>
    match c with
    | .nan => .nan
    | .inf s' => if s = s' then .inf s else .nan
    | .zero _ => .inf s
    | .num _ => .inf s
  | .zero s =>
    match c with
    | .nan => .nan
    | .inf s' => .inf s'
    | .zero s' => .zero (s && s')
    | .num w => R w
  | .num pr =>
    match c with
    | .nan => .nan
    | .inf s' => .inf s'
    | .zero _ => R pr
    | .num w => if pr + w = 0 then .zero false else R (pr + w)

/-! ### Special operands (Theorem B, item 3) -/

/-- If `zl`, `zh` and `y` have the same sign, the kernel `fma(x, zh, x*zl)` returns `x / y` for
every `x` that is a zero, an infinity or a NaN. -/
theorem kernel_special (R : ℚ → IEEE) {x : IEEE} {zh zl y : ℚ} (hx : ∀ v, x ≠ IEEE.num v)
    (_hy : y ≠ 0) (_hzh : zh ≠ 0) (_hzl : zl ≠ 0)
    (h1 : sgn zh = sgn y) (h2 : sgn zl = sgn zh) :
    fma R x (IEEE.num zh) (mul R x (IEEE.num zl)) = div R x (IEEE.num y) := by
  cases x with
  | nan => simp [fma, mul, div]
  | inf s => simp [fma, mul, div, h2, h1]
  | zero s => simp [fma, mul, div, h2, h1]
  | num v => exact absurd rfl (hx v)

/-- With `zl` and `zh` of opposite signs the kernel turns an infinity into NaN. -/
theorem kernel_inf_opposite (R : ℚ → IEEE) (s : Bool) {zh zl : ℚ} (_hzh : zh ≠ 0) (_hzl : zl ≠ 0)
    (h : sgn zl ≠ sgn zh) :
    fma R (IEEE.inf s) (IEEE.num zh) (mul R (IEEE.inf s) (IEEE.num zl)) = IEEE.nan := by
  cases s <;> cases h1 : sgn zh <;> cases h2 : sgn zl <;> simp_all [fma, mul]

/-- With `zl` and `zh` of opposite signs the kernel returns `+0` for both zeros. -/
theorem kernel_zero_opposite (R : ℚ → IEEE) (s : Bool) {zh zl : ℚ} (_hzh : zh ≠ 0) (_hzl : zl ≠ 0)
    (h : sgn zl ≠ sgn zh) :
    fma R (IEEE.zero s) (IEEE.num zh) (mul R (IEEE.zero s) (IEEE.num zl)) = IEEE.zero false := by
  cases s <;> cases h1 : sgn zh <;> cases h2 : sgn zl <;> simp_all [fma, mul]

/-! ### Power-of-two divisors (Theorem B, item 2) -/

theorem sgn_of_mul_eq_one {y zh : ℚ} (h : y * zh = 1) : sgn zh = sgn y := by
  have hy : y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  have hz : zh = y⁻¹ := eq_inv_of_mul_eq_one_right h
  simp only [sgn, hz, inv_lt_zero]

/-- If `y * zh = 1` exactly (so `y` is a power of two), `x * zh` and `x / y` are the same IEEE
datum for every `x`, whatever the rounding function. -/
theorem mul_inv_eq_div (R : ℚ → IEEE) {y zh : ℚ} (h : y * zh = 1) (x : IEEE) :
    mul R x (IEEE.num zh) = div R x (IEEE.num y) := by
  have hs := sgn_of_mul_eq_one h
  have hz : zh = y⁻¹ := eq_inv_of_mul_eq_one_right h
  cases x with
  | nan => simp [mul, div]
  | inf s => simp [mul, div, hs]
  | zero s => simp [mul, div, hs]
  | num u => simp [mul, div, hz, div_eq_mul_inv]

/-! ### Facts about `IsNearestB` and `RoundSpec` -/

theorem IsNearestB.neg {p : ℕ} {emin : ℤ} {t f : ℚ} (h : IsNearestB p emin t f) :
    IsNearestB p emin (-t) (-f) := by
  refine ⟨h.1.neg, fun g hg => ?_⟩
  have h1 := h.2 (-g) hg.neg
  have e1 : -t - -f = -(t - f) := by ring
  have e2 : -t - g = -(t - -g) := by ring
  rw [e1, e2, abs_neg, abs_neg]; exact h1

theorem IsNearestB.le_of_le {p : ℕ} {emin : ℤ} {t f B : ℚ} (h : IsNearestB p emin t f)
    (hB : IsFloatB p emin B) (hle : t ≤ B) : f ≤ B := by
  by_contra hf
  push Not at hf
  have h1 := h.2 B hB
  rw [abs_of_nonpos (by linarith : t - f ≤ 0), abs_of_nonpos (by linarith : t - B ≤ 0)] at h1
  linarith

theorem IsNearestB.ge_of_ge {p : ℕ} {emin : ℤ} {t f B : ℚ} (h : IsNearestB p emin t f)
    (hB : IsFloatB p emin B) (hle : B ≤ t) : B ≤ f := by
  by_contra hf
  push Not at hf
  have h1 := h.2 B hB
  rw [abs_of_nonneg (by linarith : 0 ≤ t - f), abs_of_nonneg (by linarith : 0 ≤ t - B)] at h1
  linarith

/-- a nearest float of `t` is within `[-B, B]` when `|t| ≤ B` and `B` is a float -/
theorem IsNearestB.abs_le {p : ℕ} {emin : ℤ} {t f B : ℚ} (h : IsNearestB p emin t f)
    (hB : IsFloatB p emin B) (hle : |t| ≤ B) : |f| ≤ B := by
  have h1 := _root_.abs_le.mp hle
  exact _root_.abs_le.mpr ⟨h.ge_of_ge hB.neg h1.1, h.le_of_le hB h1.2⟩

/-- a nearest float of `t` has magnitude at least `B` when `|t| ≥ B` and `B` is a float -/
theorem IsNearestB.le_abs {p : ℕ} {emin : ℤ} {t f B : ℚ} (h : IsNearestB p emin t f)
    (hB : IsFloatB p emin B) (hle : B ≤ |t|) : B ≤ |f| := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at hle
    exact le_trans (h.ge_of_ge hB hle) (le_abs_self f)
  · rw [abs_of_neg h0] at hle
    have h1 : f ≤ -B := h.le_of_le hB.neg (by linarith)
    exact le_trans (by linarith) (neg_le_abs f)

theorem minNormal_pos (p : ℕ) (emin : ℤ) : 0 < minNormal p emin := by
  unfold minNormal; positivity

/-- A nonzero float of the format that is not too large rounds to itself. -/
theorem RoundSpec.of_float {p : ℕ} {emin emax : ℤ} {t : ℚ} {r : IEEE}
    (h : RoundSpec p emin emax t r) (ht : IsFloatB p emin t) (ht0 : t ≠ 0)
    (hmax : |t| ≤ maxFloat p emax) : r = IEEE.num t := by
  obtain ⟨f, hf, hcase⟩ := h
  have h0 := hf.2 t ht
  rw [sub_self, abs_zero] at h0
  have hft : t - f = 0 := abs_nonpos_iff.mp h0
  have hft' : f = t := by linarith
  rw [hft'] at hcase
  rcases hcase with ⟨hz, -⟩ | ⟨-, -, hr⟩ | ⟨hgt, -⟩
  · exact absurd hz ht0
  · exact hr
  · exact absurd hmax (not_le.mpr hgt)

/-- A finite nonzero result is a nearest float of the exact value. -/
theorem RoundSpec.num_inv {p : ℕ} {emin emax : ℤ} {t v : ℚ}
    (h : RoundSpec p emin emax t (IEEE.num v)) :
    IsNearestB p emin t v ∧ v ≠ 0 ∧ |v| ≤ maxFloat p emax := by
  obtain ⟨f, hf, hcase⟩ := h
  rcases hcase with ⟨-, hr⟩ | ⟨hne, hle, hr⟩ | ⟨-, hr⟩
  · cases hr
  · cases hr; exact ⟨hf, hne, hle⟩
  · cases hr

/-- Two exact values whose nearest floats are forced to coincide and to be nonzero round to the
same IEEE datum (finite or infinite). -/
theorem RoundSpec.eq_of_unique {p : ℕ} {emin emax : ℤ} {t1 t2 : ℚ} {r1 r2 : IEEE}
    (h1 : RoundSpec p emin emax t1 r1) (h2 : RoundSpec p emin emax t2 r2)
    (hu : ∀ f1 f2, IsNearestB p emin t1 f1 → IsNearestB p emin t2 f2 → f1 = f2 ∧ f1 ≠ 0) :
    r1 = r2 := by
  obtain ⟨f1, hf1, c1⟩ := h1
  obtain ⟨f2, hf2, c2⟩ := h2
  obtain ⟨heq, hne⟩ := hu f1 f2 hf1 hf2
  rw [← heq] at c2
  rcases c1 with ⟨hz, -⟩ | ⟨-, hle, hr1⟩ | ⟨hgt, hr1⟩
  · exact absurd hz hne
  · rcases c2 with ⟨hz, -⟩ | ⟨-, -, hr2⟩ | ⟨hgt, -⟩
    · exact absurd hz hne
    · rw [hr1, hr2]
    · exact absurd hle (not_le.mpr hgt)
  · rcases c2 with ⟨hz, -⟩ | ⟨-, hle, -⟩ | ⟨-, hr2⟩
    · exact absurd hz hne
    · exact absurd hle (not_le.mpr hgt)
    · rw [hr1, hr2]

end ExactFDiv
