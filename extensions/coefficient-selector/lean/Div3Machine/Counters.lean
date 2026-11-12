import Div3Machine.Arithmetic

namespace Div3Machine

theorem minus8 (a : ℕ) (ha : a < 2^64) (h8 : 8 ≤ a) :
    BitVec.ofNat 64 a + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (a-8) := by
  have h : BitVec.ofInt 64 (-8) = -(BitVec.ofNat 64 8) := by decide +kernel
  rw [h,← BitVec.sub_eq_add_neg]
  exact bv_sub a 8 h8 ha

theorem minus1 (a : ℕ) (ha : a < 2^64) (h1 : 1 ≤ a) :
    BitVec.ofNat 64 a - 1 = BitVec.ofNat 64 (a-1) := by
  exact bv_sub a 1 h1 ha

theorem minus8Bits (a : ℕ) (ha : a < 2^64) (h8 : 8 ≤ a) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 18446744073709551608 = BitVec.ofNat 64 (a-8) := by
  have h : BitVec.ofNat 64 18446744073709551608 = BitVec.ofInt 64 (-8) := by decide +kernel
  rw [h]
  exact minus8 a ha h8

theorem setup_count (n : ℕ) (hn : n < 2^64) (h32 : 32 ≤ n) :
    ((BitVec.ofNat 64 n-BitVec.ofNat 64 32) >>> (5:ℕ))+1 = BitVec.ofNat 64 (n/32) := by
  rw [bv_sub n 32 h32 hn]
  have hshift : (BitVec.ofNat 64 (n-32) >>> (5:ℕ)) = BitVec.ofNat 64 ((n-32)/32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    have hs : n-32 < 18446744073709551616 := by omega
    have hd : (n-32)/32 < 18446744073709551616 := lt_of_le_of_lt (Nat.div_le_self _ _) hs
    rw [Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hd]
  rw [hshift]
  change BitVec.ofNat 64 ((n-32)/32)+BitVec.ofNat 64 1 = _
  rw [bv_add]
  congr 1
  omega

end Div3Machine
