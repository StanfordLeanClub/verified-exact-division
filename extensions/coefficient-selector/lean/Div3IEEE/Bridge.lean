import Selector.Scaling
import ExactFDiv.Algorithm

/- A coefficient-independent IEEE bridge. The accepted pair need not be the
nearest reciprocal and its canonical residual. Bounds are obligations checked
once per pair; they are not assumptions about the native implementation. -/
namespace CoefficientSelector
open ExactFDiv

theorem maxFloat_representable {p : ℕ} {emin emax : ℤ} (hee : emin ≤ emax) :
    IsFloatB p emin (maxFloat p emax) := by
  refine ⟨2 ^ p - 1, emax, ?_, hee, ?_⟩
  · have : (0:ℤ) < 2 ^ p := by positivity
    rw [abs_of_nonneg (by omega)]; omega
  · unfold maxFloat; push_cast; rw [zpow_natCast]

theorem round_normal {p : ℕ} (hp : 1 ≤ p) {emin emax : ℤ} (hee : emin ≤ emax)
    {z : ℚ} (hlo : minNormal p emin ≤ |z|) (hhi : |z| ≤ maxFloat p emax) :
    rneR p emin emax z = .num (rneU p z) := by
  have hn := rne_nearest hp emin z
  have hl := hn.le_abs (isFloatB_minNormal hp emin) hlo
  have hh := hn.abs_le (maxFloat_representable hee) hhi
  have hz : rne p emin z ≠ 0 := by
    intro he; rw [he,abs_zero] at hl; exact (minNormal_pos p emin).not_ge hl
  unfold rneR
  rw [if_neg hz, if_pos hh, rne_eq_rneU hlo]

/-- Transfer any unbounded-correct pair into bounded IEEE arithmetic. Both signs
and any precision/exponent bounds are supported. Overflow of the final rounded
result is allowed; the low product must remain finite and normal. -/
theorem arbitrary_pair_ieee {p : ℕ} (hp : 1 ≤ p) {emin emax : ℤ} (hee : emin ≤ emax)
    {h l y x : ℚ}
    (hlarge : 3*|l| ≤ |h|) (hquot : |l| ≤ 1/|y|)
    (hlo : minNormal p emin ≤ |x*l|) (hhi : |x*l| ≤ maxFloat p emax)
    (hcorrect : kernel p h l x = rneU p (x/y)) :
    fma (rneR p emin emax) (.num x) (.num h)
      (mul (rneR p emin emax) (.num x) (.num l)) =
      div (rneR p emin emax) (.num x) (.num y) := by
  have hnpos := minNormal_pos p emin
  have hmul := round_normal hp hee hlo hhi
  let t := rneU p (x*l)
  have ht := rneU_nearest hp (x*l)
  have flzero : IsFloat p 0 := ⟨0,0,by simp,by simp⟩
  have ht0 := ht.2 0 flzero
  rw [sub_zero] at ht0
  have htmag : |t| ≤ 2*|x*l| := by
    have ha := abs_sub (x*l) (x*l-t)
    rw [sub_sub_cancel] at ha
    dsimp [t] at ha ⊢
    linarith
  have htri : |x*h| ≤ |x*h+t|+|t| := by
    simpa only [add_sub_cancel_right] using abs_sub (x*h+t) t
  have hlarge' : 3*|x*l| ≤ |x*h| := by
    rw [abs_mul,abs_mul]
    have ha := mul_le_mul_of_nonneg_left hlarge (abs_nonneg x)
    nlinarith
  have hsn : minNormal p emin ≤ |x*h+t| := by linarith
  have hs0 : x*h+t ≠ 0 := by
    intro he; rw [he,abs_zero] at hsn; linarith
  have hqn : minNormal p emin ≤ |x/y| := by
    have ha := mul_le_mul_of_nonneg_left hquot (abs_nonneg x)
    rw [abs_mul] at hlo
    rw [abs_div]
    simpa only [mul_one_div] using hlo.trans ha
  have hrs : rne p emin (x*h+t) ≠ 0 := by
    have ha := (rne_nearest hp emin (x*h+t)).le_abs (isFloatB_minNormal hp emin) hsn
    intro he; rw [he,abs_zero] at ha; linarith
  have hsame : rne p emin (x*h+t) = rne p emin (x/y) := by
    rw [rne_eq_rneU hsn,rne_eq_rneU hqn]
    exact hcorrect
  change fma (rneR p emin emax) (.num x) (.num h) (rneR p emin emax (x*l)) = _
  rw [hmul]
  change (if x*h+t = 0 then IEEE.zero false else rneR p emin emax (x*h+t)) = _
  rw [if_neg hs0]
  exact rneR_congr hrs hsame

/-- Cheap sufficient bounds for a one-sided threshold covering every finite
dividend above it. No upper input guard is necessary when |l| ≤ 1. -/
theorem arbitrary_pair_guarded {p : ℕ} (hp : 1 ≤ p) {emin emax : ℤ} (hee : emin ≤ emax)
    {h l y T x : ℚ} (hx : ValidNum p emin emax x)
    (hl : |l| ≤ 1) (hlarge : 3*|l| ≤ |h|) (hquot : |l| ≤ 1/|y|)
    (hT : minNormal p emin ≤ T*|l|) (hg : T ≤ |x|)
    (hcorrect : kernel p h l x = rneU p (x/y)) :
    fma (rneR p emin emax) (.num x) (.num h)
      (mul (rneR p emin emax) (.num x) (.num l)) =
      div (rneR p emin emax) (.num x) (.num y) := by
  apply arbitrary_pair_ieee hp hee hlarge hquot _ _ hcorrect
  · rw [abs_mul]
    exact hT.trans (mul_le_mul_of_nonneg_right hg (abs_nonneg l))
  · rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg x) hl).trans hx.2.2

/-- Compose the finite checker, sign/scale theorem, and bounded IEEE bridge.
The remaining premises are explicit per-pair range obligations. -/
theorem check_sound_ieee {p : ℕ} (hp : 1 ≤ p) {emin emax : ℤ} (hee : emin ≤ emax)
    {Y X : ℤ} {c₁ c₂ : GridCert} {c : Coeff}
    (hc : check p Y c₁ c₂ c = true)
    (hX1 : (2:ℤ)^p ≤ 2*X) (hX2 : X < (2:ℤ)^p)
    {s : ℚ} (hs : s = 1 ∨ s = -1) (i j : ℤ)
    (hlarge : 3*|c.l*2^(-j)| ≤ |c.h*2^(-j)|)
    (hquot : |c.l*2^(-j)| ≤ 1/|(Y:ℚ)*2^j|)
    (hlo : minNormal p emin ≤ |(s*X*2^i)*(c.l*2^(-j))|)
    (hhi : |(s*X*2^i)*(c.l*2^(-j))| ≤ maxFloat p emax) :
    fma (rneR p emin emax) (.num (s*X*2^i)) (.num (c.h*2^(-j)))
      (mul (rneR p emin emax) (.num (s*X*2^i)) (.num (c.l*2^(-j)))) =
      div (rneR p emin emax) (.num (s*X*2^i)) (.num ((Y:ℚ)*2^j)) :=
  arbitrary_pair_ieee hp hee hlarge hquot hlo hhi (check_sound_scaled hc hX1 hX2 hs i j)

end CoefficientSelector
