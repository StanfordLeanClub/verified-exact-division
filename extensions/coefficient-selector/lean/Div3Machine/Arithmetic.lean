import Div3Machine.ISA

namespace Div3Machine
open Div3IEEE ExactFDiv
set_option maxRecDepth 3000

theorem mul_comm_value (R : ℚ → IEEE) (a b : IEEE) :
    ExactFDiv.mul R a b = ExactFDiv.mul R b a := by
  cases a <;> cases b <;> simp [ExactFDiv.mul, Bool.xor_comm, mul_comm]

theorem fma_comm_value (R : ℚ → IEEE) (a b c : IEEE) :
    ExactFDiv.fma R a b c = ExactFDiv.fma R b a c := by
  unfold ExactFDiv.fma
  rw [mul_comm_value]

def packedRaw (fp : IEEEInstructions) (w : Word) := fp.fma hiWord w (fp.mul w loWord)

theorem packedRaw_value (fp : IEEEInstructions) (w : Word) :
    decode (packedRaw fp w) = raw (decode w) := by
  rw [packedRaw,fp.fma_spec,fma_comm_value,fp.mul_spec,literal_values.1,literal_values.2.1]
  rfl

def packedResult (fp : IEEEInstructions) (fast : Bool) (w : Word) :=
  if fast then packedRaw fp w else divWord fp w

theorem packedResult_correct (fp : IEEEInstructions) (fast : Bool) (w : Word)
    (h : fast = true → tightTiny w = false) :
    decode (packedResult fp fast w) = reference (decode w) := by
  cases fast
  · exact divWord_value fp w
  · simp only [packedResult,Bool.true_eq,if_true,packedRaw_value]
    exact tight_raw_correct w (by rw [h rfl]; decide)

theorem bv_nat (n : ℕ) (h : n < 2^64) : (BitVec.ofNat 64 n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem bv_add (a b : ℕ) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a+b) := by
  simp [BitVec.ofNat_add]

theorem bv_sub (a b : ℕ) (hb : b ≤ a) (ha : a < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a-b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt (lt_of_le_of_lt hb ha)]
  have hab : a-b < 2^64 := lt_of_le_of_lt (Nat.sub_le _ _) ha
  rw [Nat.mod_eq_of_lt hab]
  have he : 2^64-b+a = (a-b)+2^64 := by omega
  rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt hab]

theorem bv_ult (a b : ℕ) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a<b) := by
  simp only [BitVec.ult_eq_decide,bv_nat _ ha,bv_nat _ hb]

theorem bv_beq (a b : ℕ) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa only [bv_nat _ ha,bv_nat _ hb] using this
  · intro h; rw [h]

end Div3Machine
