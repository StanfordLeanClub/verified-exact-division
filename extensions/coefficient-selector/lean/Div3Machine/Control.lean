import Div3Machine.Image
import Div3Machine.Scalar

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def constantReads (s : State) : List Access :=
  [⟨false,address s (.image 512),4⟩,⟨false,address s (.image 516),4⟩,
   ⟨false,address s (.image 520),4⟩,⟨false,address s (.image 524),4⟩,⟨false,address s (.image 528),4⟩]

theorem enter_effect (fp : IEEEInstructions) (s : State) :
    let t := evalBlock fp b_enter s
    t.memory = s.memory ∧ t.g = s.g ∧ t.v = s.v ∧ t.trace = s.trace ∧
    t.pc = (if (s.g 2).ult (BitVec.ofNat 64 32) then 0x118 else 0xa) := by
  simp [b_enter,evalBlock,execute,condition]
  split <;> simp_all

theorem setup32_effect (fp : IEEEInstructions) (s : State) (hc : ImageConstants s) :
    let t := evalBlock fp b_setup32 s
    t.memory = s.memory ∧ t.g 0 = 0 ∧
    t.g 1 = ((s.g 2-BitVec.ofNat 64 32) >>> (5:ℕ))+1 ∧ Constants t ∧
    t.pc = 0x50 ∧ t.trace = s.trace ++ constantReads s := by
  rcases hc with ⟨h0,h1,h3,h4,h5⟩
  simp [address] at h0 h1 h3 h4 h5
  simp [b_setup32,evalBlock,execute,setG,setV,track,Function.update_apply,address,
    h0,h1,h3,h4,h5,Constants,constantReads,List.append_assoc]
  all_goals repeat' constructor

theorem setup8_effect (fp : IEEEInstructions) (s : State) (hc : ImageConstants s) :
    let t := evalBlock fp b_setup8 s
    t.memory = s.memory ∧ t.g = s.g ∧ Constants t ∧
    t.pc = 0x160 ∧ t.trace = s.trace ++ constantReads s := by
  rcases hc with ⟨h0,h1,h3,h4,h5⟩
  simp [address] at h0 h1 h3 h4 h5
  simp [b_setup8,evalBlock,execute,setV,track,Function.update_apply,address,
    h0,h1,h3,h4,h5,Constants,constantReads,List.append_assoc]
  all_goals repeat' constructor

theorem check8_effect (fp : IEEEInstructions) (s : State) :
    let t := evalBlock fp b_check8 s
    t.memory = s.memory ∧ t.g 0 = s.g 0 ∧ t.g 1 = s.g 2-s.g 0 ∧
    t.pc = (if (s.g 2-s.g 0).ult (BitVec.ofNat 64 8) then 0x19c else 0x126) ∧
    t.trace = s.trace := by
  simp [b_check8,evalBlock,execute,setG,condition,Function.update_apply]
  split <;> simp_all

theorem check1_effect (fp : IEEEInstructions) (s : State) :
    let t := evalBlock fp b_check1 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.pc = (if (s.g 0).ult (s.g 2) then 0x1a1 else 0x1f5) ∧ t.trace = s.trace := by
  simp [b_check1,evalBlock,execute,condition]
  cases h : (s.g 0).ult (s.g 2) <;> simp [h]

theorem setup1_effect (fp : IEEEInstructions) (s : State) (hc : ImageConstants s) :
    let t := evalBlock fp b_setup1 s
    t.memory = s.memory ∧ t.g = s.g ∧ ScalarConstants t ∧ t.pc = 0x1cd ∧
    t.trace = s.trace ++ [⟨false,address s (.image 524),4⟩,
      ⟨false,address s (.image 528),4⟩,⟨false,address s (.image 520),4⟩] := by
  rcases hc with ⟨h0,h1,h3,h4,h5⟩
  simp [address] at h3 h4 h5
  simp [b_setup1,evalBlock,execute,setV,track,Function.update_apply,address,
    h3,h4,h5,ScalarConstants,List.append_assoc]

theorem skip32_effect (fp : IEEEInstructions) (s : State) :
    let t := evalBlock fp b_skip32 s
    t.memory = s.memory ∧ t.g 0 = 0 ∧ t.pc = 0x11a ∧ t.trace = s.trace := by
  simp [b_skip32,evalBlock,execute,setG]

theorem exit32_effect (fp : IEEEInstructions) (s : State) :
    evalBlock fp b_exit32 s = {s with pc := 0x11a} := rfl

theorem exit8_effect (fp : IEEEInstructions) (s : State) :
    evalBlock fp b_exit8 s = {s with pc := 0x19c} := rfl

theorem return_effect (fp : IEEEInstructions) (s : State) :
    let t := evalBlock fp b_exit s
    t.memory = s.memory ∧ t.pc = (read64 s.memory (s.g 4).toNat).toNat ∧
    t.halted = true ∧ t.invalid = s.invalid ∧ t.g 4 = s.g 4+8 ∧
    (∀ r, r ≠ 4 → t.g r = s.g r) ∧
    t.trace = s.trace ++ [⟨false,(s.g 4).toNat,8⟩] := by
  simp [b_exit,evalBlock,execute,setG,track,Function.update_apply]
  intro r hr
  simp [hr]

end Div3Machine
