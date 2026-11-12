import Div3Machine.Support

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem guard8_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : address s (.indexed 6 0 4 0) = a) (hc : Constants s) :
    let t := evalBlock fp b_guard8 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 6 = readVec s.memory a ∧
    t.pc = (if all8 (fun j => compiledFast (readVec s.memory a j)) then 0x178 else 0x196) ∧
    t.trace = s.trace ++ [⟨false,a,32⟩] := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  have hv : (fun i : Fin 8 => if i.val < 8 then read32 s.memory (a+4*i.val) else 0) =
      readVec s.memory a := by funext i; simp [readVec,i.isLt]
  simp [b_guard8,evalBlock,execute,setV,track,condition,Function.update_apply]
  simp only [address,Nat.add_zero] at ha
  simp only [address,Nat.add_zero,ha,h0,h1,h2,hv,Fin.isLt,ite_true]
  have hf := ptest_compare (fun j => compiledFast (readVec s.memory a j))
  simp only [compiledFast,doubled,readVec,
    show (0xffffffff : Word) = BitVec.ofNat 32 0xffffffff by rfl,
    show (0 : Word) = BitVec.ofNat 32 0 by rfl] at hf
  simp only [cmpMask,hf]
  cases he : all8 (fun j => compiledFast (readVec s.memory a j)) <;>
    simp only [compiledFast,doubled,readVec] at he <;>
    simp [he,readVec,hf] <;> rfl

theorem fast8_effect (fp : IEEEInstructions) (s : State) (hc : Constants s) :
    let t := evalBlock fp b_fast8 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 7 = (fun j => packedRaw fp (s.v 6 j)) ∧
    t.pc = 0x181 ∧ t.trace = s.trace := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [b_fast8,evalBlock,execute,setV,fpWrite,Function.update_apply,h4,h5,packedRaw]
  funext j; rfl

theorem slow8_effect (fp : IEEEInstructions) (s : State) (hc : Constants s) :
    let t := evalBlock fp b_slow8 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 7 = (fun j => divWord fp (s.v 6 j)) ∧
    t.pc = 0x181 ∧ t.trace = s.trace := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [b_slow8,evalBlock,execute,setV,fpWrite,Function.update_apply,h3,divWord]
  funext j; rfl

theorem guard8_safe (m : Memory) (a : ℕ) (j : Fin 8)
    (h : all8 (fun j => compiledFast (readVec m a j)) = true) :
    tightTiny (readVec m a j) = false := by
  have h' : ∀ j, compiledFast (readVec m a j) = true := by simpa [all8] using h
  simpa [compiledFast_eq] using h' j

end Div3Machine
