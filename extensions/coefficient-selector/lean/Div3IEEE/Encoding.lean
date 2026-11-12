import Div3IEEE.Core

namespace Div3IEEE
open ExactFDiv
deriving instance DecidableEq for IEEE

def significand (e f : ℕ) : ℕ := if e = 0 then f else 8388608+f
def quantum (e : ℕ) : ℤ := if e = 0 then -149 else (e:ℤ)-150
def magnitude (e f : ℕ) : ℚ := (significand e f : ℚ)*(2:ℚ)^quantum e
def withSign (s : Bool) (v : ℚ) : ℚ := if s then -v else v

/-- Standard binary32 decoding; NaN sign, payload, and signaling status are
intentionally collapsed to the NaN class of the existing IEEE value model. -/
def decodeFields (s : Bool) (e f : ℕ) : IEEE :=
  if e = 255 then (if f = 0 then .inf s else .nan)
  else if e = 0 ∧ f = 0 then .zero s
  else .num (withSign s (magnitude e f))

def exponent (w : BitVec 32) : ℕ := w.toNat / 8388608 % 256
def fraction (w : BitVec 32) : ℕ := w.toNat % 8388608
def decode (w : BitVec 32) : IEEE := decodeFields w.msb (exponent w) (fraction w)

theorem magnitude_nonneg (e f : ℕ) : 0 ≤ magnitude e f := by
  unfold magnitude; positivity

theorem abs_withSign (s : Bool) {v : ℚ} (hv : 0 ≤ v) : |withSign s v| = v := by
  cases s <;> simp [withSign,abs_of_nonneg hv]

theorem dyadic_valid (s : Bool) {m : ℕ} {e : ℤ} (hm0 : 0 < m) (hm1 : m < 16777216)
    (he0 : -149 ≤ e) (he1 : e ≤ 104) :
    ValidNum 24 (-149) 104 (withSign s ((m:ℚ)*(2:ℚ)^e)) := by
  have hmpos : (0:ℚ) < m := by exact_mod_cast hm0
  have hvpos : (0:ℚ) < m*(2:ℚ)^e := mul_pos hmpos (two_zpow_pos e)
  have hf : IsFloatB 24 (-149) ((m:ℚ)*(2:ℚ)^e) := by
    refine ⟨(m:ℤ),e,?_,he0,by simp⟩
    rw [abs_of_nonneg (Int.natCast_nonneg m)]
    norm_num; exact_mod_cast hm1
  have hmle : (m:ℚ) ≤ 16777215 := by exact_mod_cast (show m ≤ 16777215 by omega)
  have hpow : (2:ℚ)^e ≤ (2:ℚ)^(104:ℤ) := zpow_le_zpow_right₀ (by norm_num) he1
  have hmax : |(m:ℚ)*(2:ℚ)^e| ≤ maxFloat 24 104 := by
    rw [abs_of_pos hvpos]
    have h := mul_le_mul hmle hpow (two_zpow_pos e).le (by norm_num)
    norm_num [maxFloat] at h ⊢
    exact h
  cases s
  · exact ⟨hvpos.ne',hf,hmax⟩
  · exact ⟨neg_ne_zero.mpr hvpos.ne',hf.neg,by simpa [withSign,abs_neg] using hmax⟩

theorem decodeFields_valid (s : Bool) {e f : ℕ} (he : e < 256) (hf : f < 8388608) :
    valid32 (decodeFields s e f) := by
  by_cases hi : e = 255
  · by_cases hz : f = 0 <;> simp [decodeFields,hi,hz,valid32,Valid]
  by_cases hz : e = 0 ∧ f = 0
  · simp [decodeFields,hi,hz,valid32,Valid]
  simp only [decodeFields,if_neg hi,if_neg hz]
  apply dyadic_valid
  · unfold significand; split_ifs <;> omega
  · unfold significand; split_ifs <;> omega
  · unfold quantum; split_ifs <;> omega
  · unfold quantum; split_ifs <;> omega

theorem decode_valid (w : BitVec 32) : valid32 (decode w) := by
  exact decodeFields_valid w.msb (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem magnitude_lt_threshold {e f : ℕ} (he : e < 255) (hf : f < 8388608) :
    magnitude e f < threshold ↔ e < 27 := by
  by_cases hz : e = 0
  · subst e
    have hfq : (f:ℚ) < 8388608 := by exact_mod_cast hf
    have h := mul_lt_mul_of_pos_right hfq (two_zpow_pos (-149))
    have h1 : (8388608:ℚ)*(2:ℚ)^(-149:ℤ) < threshold := by norm_num [threshold]
    simpa [magnitude,significand,quantum] using h.trans h1
  have hm0 : (0:ℚ) ≤ (8388608+f:ℕ) := by positivity
  have hmlo : (8388608:ℚ) ≤ (8388608+f:ℕ) := by exact_mod_cast (show 8388608 ≤ 8388608+f by omega)
  have hmhi : ((8388608+f:ℕ):ℚ) < 16777216 := by exact_mod_cast (show 8388608+f < 16777216 by omega)
  by_cases hsmall : e < 27
  · have heq : (e:ℤ)-150 ≤ -124 := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) heq
    have h1 := mul_lt_mul_of_pos_right hmhi (two_zpow_pos ((e:ℤ)-150))
    have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℚ) ≤ 16777216)
    have h3 : (16777216:ℚ)*(2:ℚ)^(-124:ℤ) = threshold := by norm_num [threshold]
    rw [h3] at h2
    simp only [magnitude,significand,quantum,if_neg hz]
    exact ⟨fun _ => hsmall,fun _ => lt_of_lt_of_le h1 h2⟩
  · have heq : (-123:ℤ) ≤ (e:ℤ)-150 := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) heq
    have h1 := mul_le_mul hmlo hp (two_zpow_pos (-123)).le hm0
    have h2 : (8388608:ℚ)*(2:ℚ)^(-123:ℤ) = threshold := by norm_num [threshold]
    have hge : threshold ≤ magnitude e f := by
      simpa only [h2,magnitude,significand,quantum,if_neg hz] using h1
    exact ⟨fun h => False.elim (h.not_ge hge),fun h => False.elim (hsmall h)⟩

theorem tiny_decodeFields (s : Bool) {e f : ℕ} (he : e < 256) (hf : f < 8388608) :
    tiny (decodeFields s e f) = decide (0 < e*8388608+f ∧ e < 27) := by
  by_cases hi : e = 255
  · by_cases hz : f = 0 <;> simp [decodeFields,hi,hz,tiny]
  by_cases hz : e = 0 ∧ f = 0
  · rcases hz with ⟨rfl,rfl⟩; simp [decodeFields,tiny]
  have hp : 0 < e*8388608+f := by omega
  simp only [decodeFields,if_neg hi,if_neg hz,tiny,abs_withSign s (magnitude_nonneg e f)]
  simp only [magnitude_lt_threshold (e:=e) (f:=f) (by omega) hf,hp,true_and]

theorem fields_identity (w : BitVec 32) :
    w.toNat % 2147483648 = exponent w * 8388608 + fraction w := by
  unfold exponent fraction
  omega

theorem tiny_decode (w : BitVec 32) :
    tiny (decode w) = decide (0 < w.toNat % 2147483648 ∧ w.toNat % 2147483648 < 226492416) := by
  unfold decode
  rw [tiny_decodeFields w.msb (e:=exponent w) (f:=fraction w)
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  have hi := fields_identity w
  have hf : fraction w < 8388608 := Nat.mod_lt _ (by norm_num)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

/-- All binary32 encodings, with no caller-supplied float-validity premise. -/
theorem decoded_correct (w : BitVec 32) : guarded (decode w) = reference (decode w) :=
  guarded_correct _ (decode_valid w)

end Div3IEEE
