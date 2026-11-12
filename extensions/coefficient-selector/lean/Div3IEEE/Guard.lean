import Div3IEEE.Encoding

namespace Div3IEEE
open ExactFDiv

theorem shifted_magnitude (w : BitVec 32) :
    (w <<< (1:ℕ)).toNat = 2*(w.toNat % 2147483648) := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  exact (Nat.mul_mod_mul_right 2 w.toNat 2147483648).trans (Nat.mul_comm _ _)

/-- The exact AVX2 P4 same-sign test: signed(Cz) > signed((bits << 1) + K2).
All shifts and additions here are actual 32-bit wrapping BitVec operations. -/
def nativeTiny (w : BitVec 32) : Bool :=
  ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff).slt (BitVec.ofNat 32 0x9affffff)

theorem nativeTiny_bits (w : BitVec 32) : nativeTiny w =
    decide (0 < w.toNat % 2147483648 ∧ w.toNat % 2147483648 < 226492416) := by
  unfold nativeTiny
  rw [BitVec.slt_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hm : w.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have ht : ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff).toNat =
      (2*(w.toNat % 2147483648)+2147483647)%4294967296 := by
    rw [BitVec.toNat_add,shifted_magnitude]
    rfl
  have hc : (BitVec.ofNat 32 0x9affffff).toInt = (-1694498817:ℤ) := by decide +kernel
  rw [hc,BitVec.toInt_eq_toNat_cond,ht]
  norm_num only [Nat.reducePow]
  split_ifs <;> omega

theorem nativeTiny_eq (w : BitVec 32) : nativeTiny w = tiny (decode w) := by
  rw [nativeTiny_bits,tiny_decode]

/-- The out-of-range mask recomputed by efd32_block_slow. -/
def nativeOut (w : BitVec 32) : Bool :=
  (BitVec.ofNat 32 0x63ffffff).slt ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x65000000)

/-- Its special-lane mask: signed zeros, infinities and all NaN encodings. -/
def nativeSpecial (w : BitVec 32) : Bool :=
  (BitVec.ofNat 32 0x7efffffe).slt ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff)

def coldTiny (w : BitVec 32) : Bool := nativeOut w && !nativeSpecial w

theorem nativeOut_bits (w : BitVec 32) : nativeOut w =
    decide (w.toNat % 2147483648 < 226492416 ∨ 2139095040 ≤ w.toNat % 2147483648) := by
  unfold nativeOut
  rw [BitVec.slt_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hm : w.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have ht : ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x65000000).toNat =
      (2*(w.toNat % 2147483648)+1694498816)%4294967296 := by
    rw [BitVec.toNat_add,shifted_magnitude]
    rfl
  have hc : (BitVec.ofNat 32 0x63ffffff).toInt = (1677721599:ℤ) := by decide +kernel
  rw [hc,BitVec.toInt_eq_toNat_cond,ht]
  norm_num only [Nat.reducePow]
  split_ifs <;> omega

theorem nativeSpecial_bits (w : BitVec 32) : nativeSpecial w =
    decide (w.toNat % 2147483648 = 0 ∨ 2139095040 ≤ w.toNat % 2147483648) := by
  unfold nativeSpecial
  rw [BitVec.slt_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hm : w.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have ht : ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff).toNat =
      (2*(w.toNat % 2147483648)+2147483647)%4294967296 := by
    rw [BitVec.toNat_add,shifted_magnitude]
    rfl
  have hc : (BitVec.ofNat 32 0x7efffffe).toInt = (2130706430:ℤ) := by decide +kernel
  rw [hc,BitVec.toInt_eq_toNat_cond,ht]
  norm_num only [Nat.reducePow]
  split_ifs <;> omega

/-- A flagged same-sign P4 block always takes the division arm of block_slow. -/
theorem coldTiny_eq (w : BitVec 32) : coldTiny w = nativeTiny w := by
  unfold coldTiny
  rw [nativeOut_bits,nativeSpecial_bits,nativeTiny_bits]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
  omega

def nativeGuarded (w : BitVec 32) : IEEE :=
  if nativeTiny w then reference (decode w) else raw (decode w)

theorem nativeGuarded_correct (w : BitVec 32) : nativeGuarded w = reference (decode w) := by
  unfold nativeGuarded
  rw [nativeTiny_eq]
  exact decoded_correct w

/-- Connect the exact literals in the C context to the rational constants in the proof. -/
theorem coefficient_encodings :
    decode (BitVec.ofNat 32 0x3eaaaaaa) = .num hi ∧
    decode (BitVec.ofNat 32 0x32aaaaab) = .num lo ∧
    decode (BitVec.ofNat 32 0x0d800000) = .num threshold ∧
    decode (BitVec.ofNat 32 0x40400000) = .num 3 := by decide +kernel

end Div3IEEE
