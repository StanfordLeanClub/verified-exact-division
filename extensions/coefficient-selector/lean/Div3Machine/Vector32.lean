import Div3Machine.Vector8

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def fast32 (m : Memory) (a : ℕ) : Bool := all8 (fun j =>
  (BitVec.ofNat 32 0x9a7ffffe).slt
    (smin (smin (doubled (readVec m (a+32) j)) (doubled (readVec m a j)))
      (smin (doubled (readVec m (a+64) j)) (doubled (readVec m (a+96) j)))))

def reads32 (a : ℕ) : List Access :=
  [⟨false,a,32⟩,⟨false,a+64,32⟩,⟨false,a+32,32⟩,⟨false,a+96,32⟩,
   ⟨false,a,32⟩,⟨false,a+32,32⟩,⟨false,a+64,32⟩,⟨false,a+96,32⟩]

theorem guard32_effect (fp : IEEEInstructions) (s : State) (a : ℕ)
    (ha : ∀ off ∈ [0,32,64,96], address s (.indexed 6 0 4 off) = a+off)
    (hc : Constants s) :
    let t := evalBlock fp b_guard32 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 10 = readVec s.memory a ∧ t.v 9 = readVec s.memory (a+32) ∧
    t.v 7 = readVec s.memory (a+64) ∧ t.v 6 = readVec s.memory (a+96) ∧
    t.pc = (if fast32 s.memory a then 0xbc else 0x106) ∧
    t.trace = s.trace ++ reads32 a := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  have hv (b : ℕ) : (fun i : Fin 8 => if i.val < 8 then read32 s.memory (b+4*i.val) else 0) =
      readVec s.memory b := by funext i; simp [readVec,i.isLt]
  have ha0 := ha 0 (by simp)
  have ha32 := ha 32 (by simp)
  have ha64 := ha 64 (by simp)
  have ha96 := ha 96 (by simp)
  simp only [address,Nat.add_zero] at ha0 ha32 ha64 ha96
  simp [b_guard32,evalBlock,execute,setV,track,condition,Function.update_apply]
  simp only [address,Nat.add_zero,ha0,ha32,ha64,ha96,h0,h1,h2,hv,Fin.isLt,ite_true]
  have hf := ptest_compare (fun j =>
    (BitVec.ofNat 32 0x9a7ffffe).slt
      (smin (smin (doubled (readVec s.memory (a+32) j)) (doubled (readVec s.memory a j)))
        (smin (doubled (readVec s.memory (a+64) j)) (doubled (readVec s.memory (a+96) j)))))
  simp only [doubled,readVec,
    show (0xffffffff : Word) = BitVec.ofNat 32 0xffffffff by rfl,
    show (0 : Word) = BitVec.ofNat 32 0 by rfl] at hf
  simp only [cmpMask,hf]
  cases he : fast32 s.memory a <;>
    simp only [fast32,doubled,readVec] at he <;>
    simp [fast32,doubled,readVec,he,hf,reads32,List.append_assoc] <;>
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem fast32_effect (fp : IEEEInstructions) (s : State) (hc : Constants s) :
    let t := evalBlock fp b_fast32 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 8 = (fun j => packedRaw fp (s.v 10 j)) ∧
    t.v 10 = (fun j => packedRaw fp (s.v 9 j)) ∧
    t.v 9 = (fun j => packedRaw fp (s.v 7 j)) ∧
    t.v 7 = (fun j => packedRaw fp (s.v 6 j)) ∧
    t.pc = 0xe0 ∧ t.trace = s.trace := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [b_fast32,evalBlock,execute,setV,fpWrite,Function.update_apply,h4,h5,packedRaw]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem slow32_effect (fp : IEEEInstructions) (s : State) (hc : Constants s) :
    let t := evalBlock fp b_slow32 s
    t.memory = s.memory ∧ t.g = s.g ∧
    t.v 8 = (fun j => divWord fp (s.v 10 j)) ∧
    t.v 10 = (fun j => divWord fp (s.v 9 j)) ∧
    t.v 9 = (fun j => divWord fp (s.v 7 j)) ∧
    t.v 7 = (fun j => divWord fp (s.v 6 j)) ∧
    t.pc = 0xe0 ∧ t.trace = s.trace := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [b_slow32,evalBlock,execute,setV,fpWrite,Function.update_apply,h3,divWord]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem guard32_safe (m : Memory) (a : ℕ) (j : Fin 8) (h : fast32 m a = true) :
    tightTiny (readVec m a j) = false ∧ tightTiny (readVec m (a+32) j) = false ∧
    tightTiny (readVec m (a+64) j) = false ∧ tightTiny (readVec m (a+96) j) = false := by
  simp only [fast32,compiled_four_guard,all8,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact ⟨(h j).1.2,(h j).1.1,(h j).2.1,(h j).2.2⟩

end Div3Machine
