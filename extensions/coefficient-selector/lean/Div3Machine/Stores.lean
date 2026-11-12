import Div3Machine.Support

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def fourStores (m : Memory) (a : ℕ) (w x y z : Vec) : Memory :=
  writeVec (writeVec (writeVec (writeVec m a w) (a+32) x) (a+64) y) (a+96) z

theorem store32_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : ∀ off ∈ [0,32,64,96], address s (.indexed 7 0 4 off) = a+off) :
    let t := evalBlock fp b_store32 s
    t.memory = fourStores s.memory a (s.v 8) (s.v 10) (s.v 9) (s.v 7) ∧
    t.g 0 = s.g 0 + BitVec.ofNat 64 32 ∧ t.g 1 = s.g 1 - 1 ∧
    t.pc = (if s.g 1 - 1 == 0 then 0x104 else 0x50) ∧
    t.trace = s.trace ++ [⟨true,a,32⟩,⟨true,a+32,32⟩,⟨true,a+64,32⟩,⟨true,a+96,32⟩] := by
  have ha0 := ha 0 (by simp)
  have ha32 := ha 32 (by simp)
  have ha64 := ha 64 (by simp)
  have ha96 := ha 96 (by simp)
  simp only [address,Nat.add_zero] at ha0 ha32 ha64 ha96
  simp [b_store32,evalBlock,execute,setG,track,condition,Function.update_apply,
    address,ha0,ha32,ha64,ha96,fourStores,writeVec,List.length_ofFn,List.take_length]
  split <;> simp_all [List.append_assoc]

theorem store8_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : address s (.indexed 7 0 4 0) = a) :
    let t := evalBlock fp b_store8 s
    let r := s.g 1 + BitVec.ofNat 64 18446744073709551608
    t.memory = writeVec s.memory a (s.v 7) ∧
    t.g 0 = s.g 0 + BitVec.ofNat 64 8 ∧ t.g 1 = r ∧
    t.pc = (if (BitVec.ofNat 64 7).ult r then 0x160 else 0x194) ∧
    t.trace = s.trace ++ [⟨true,a,32⟩] := by
  simp only [address,Nat.add_zero] at ha
  have hc (r : Reg64) : (!r.ult 7 && !(r == 7)) = (7:Reg64).ult r := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.not_eq_true',BitVec.ult_eq_decide,
      decide_eq_true_eq,decide_eq_false_iff_not,beq_eq_false_iff_ne]
    constructor
    · rintro ⟨h,hne⟩
      have hn : r.toNat ≠ (7:Reg64).toNat := by intro he; exact hne (BitVec.eq_of_toNat_eq he)
      omega
    · intro h
      exact ⟨by omega,fun he => by rw [he] at h; omega⟩
  simp [b_store8,evalBlock,execute,setG,track,condition,Function.update_apply,address,ha,
    writeVec,List.length_ofFn,List.take_length]
  try simp only [hc]
  split <;> simp_all
  · rename_i h
    rw [BitVec.ult_eq_decide,decide_eq_true_eq]
    have hne : (s.g 1 + BitVec.ofNat 64 18446744073709551608).toNat ≠ (BitVec.ofNat 64 7).toNat := by
      intro he
      exact h.2 (BitVec.eq_of_toNat_eq he)
    have hh := h.1
    simp only [BitVec.ult_eq_decide,decide_eq_false_iff_not] at hh
    omega
  · rename_i h
    rw [BitVec.ult_eq_decide,decide_eq_false_iff_not]
    intro he
    have hh : (s.g 1 + BitVec.ofNat 64 18446744073709551608).ult (BitVec.ofNat 64 7) = false := by
      rw [BitVec.ult_eq_decide,decide_eq_false_iff_not]
      omega
    have heq := h hh
    have := congrArg BitVec.toNat heq
    omega

theorem store1_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : address s (.indexed 7 0 4 0) = a) :
    let t := evalBlock fp b_store1 s
    t.memory = write32 s.memory a (s.v 4 0) ∧
    t.g 0 = s.g 0 + 1 ∧
    t.pc = (if s.g 2 == s.g 0 + 1 then 0x1f5 else 0x1cd) ∧
    t.trace = s.trace ++ [⟨true,a,4⟩] := by
  simp only [address,Nat.add_zero] at ha
  have hw (v : Vec) : (List.ofFn v).take 1 = [v 0] := by
    rw [List.ofFn_succ]; rfl
  simp [b_store1,evalBlock,execute,setG,track,condition,Function.update_apply,address,ha,hw,writeWords]
  split <;> simp_all

end Div3Machine
