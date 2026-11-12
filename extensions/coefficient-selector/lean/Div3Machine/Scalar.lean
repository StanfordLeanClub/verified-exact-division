import Div3Machine.Support

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def ScalarConstants (s : State) : Prop := s.v 0 0 = loWord ∧ s.v 1 0 = hiWord ∧ s.v 2 0 = threeWord

theorem above_not_ule {n : ℕ} (a b : BitVec n) : (!a.ult b && !(a == b)) = !a.ule b := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',BitVec.ult_eq_decide,BitVec.ule_eq_decide,
    decide_eq_false_iff_not,beq_eq_false_iff_ne]
  have he : a = b ↔ a.toNat = b.toNat := ⟨fun h => congrArg BitVec.toNat h,BitVec.eq_of_toNat_eq⟩
  simp only [ne_eq,he]
  omega

theorem guard1_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : address s (.indexed 6 0 4 0) = a) (hc : ScalarConstants s) :
    let t := evalBlock fp b_guard1 s
    t.memory = s.memory ∧ t.g 0 = s.g 0 ∧
    t.v 3 0 = read32 s.memory a ∧ t.v 4 0 = rawWord fp (read32 s.memory a) ∧
    t.pc = (if scalarTiny (read32 s.memory a) then 0x1ef else 0x1c0) ∧
    t.trace = s.trace ++ [⟨false,a,4⟩] := by
  rcases hc with ⟨h0,h1,h2⟩
  simp [address] at ha
  simp [b_guard1,evalBlock,execute,setG,setV,track,condition,Function.update_apply,address,ha,
    fpWrite,h0,h1,rawWord,BitVec.setWidth_setWidth]
  have hp := Bool.eq_iff_iff.mp (above_not_ule
    ((read32 s.memory a &&& BitVec.ofNat 32 0x7fffffff)-BitVec.ofNat 32 1)
    (BitVec.ofNat 32 0x0d3ffffe))
  simp only [Bool.and_eq_true,Bool.not_eq_true',beq_eq_false_iff_ne] at hp
  simp only [hp]
  cases he : scalarTiny (read32 s.memory a) <;>
    simp [scalarTiny] at he <;> simp [he,fpWrite,h0,h1,rawWord]

theorem slow1_effect (fp : IEEEInstructions) (s : State) (hc : ScalarConstants s) :
    let t := evalBlock fp b_slow1 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 4 0 = divWord fp (s.v 3 0) ∧ t.pc = 0x1c0 ∧ t.trace = s.trace := by
  rcases hc with ⟨h0,h1,h2⟩
  simp [b_slow1,evalBlock,execute,setV,fpWrite,h2,divWord]

theorem scalar_constants_preserved (fp : IEEEInstructions) (xs : List Located) (s : State)
    (hm : ∀ r : Fin 3, ∀ x ∈ xs, vDest x.instruction ≠ some r.val ∧ x.instruction ≠ .zeroUpper)
    (hc : ScalarConstants s) : ScalarConstants (evalBlock fp xs s) := by
  unfold ScalarConstants at *
  simpa only [block_v fp xs s 0 (hm 0),block_v fp xs s 1 (hm 1),block_v fp xs s 2 (hm 2)] using hc

end Div3Machine
