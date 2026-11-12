import Div3Machine.ISA

namespace Div3Machine

def fallsThrough : Instruction → Bool
  | .branch .. | .jump .. | .ret => false
  | _ => true

theorem execute_linear (fp : IEEEInstructions) (op : Instruction) (s : State)
    (h : fallsThrough op = true) :
    (execute fp op s).pc = s.pc ∧ (execute fp op s).halted = s.halted ∧
      (execute fp op s).invalid = s.invalid := by
  cases op <;> simp_all [fallsThrough,execute,setG,setV,track]

def blockOK (code : List Located) : List Located → Bool
  | [] => true
  | [x] => fetch code x.pc == some x
  | x::y::xs => (fetch code x.pc == some x) && fallsThrough x.instruction &&
      (x.pc+x.length == y.pc) && blockOK code (y::xs)

def evalBlock (fp : IEEEInstructions) : List Located → State → State
  | [],s => s
  | x::xs,s => evalBlock fp xs (execute fp x.instruction {s with pc := x.pc+x.length})

theorem run_block (fp : IEEEInstructions) (code : List Located) (xs : List Located)
    (s : State) (h : blockOK code xs = true)
    (hpc : ∀ x, xs.head? = some x → s.pc = x.pc)
    (hh : s.halted = false) (he : s.invalid = false) :
    run fp code xs.length s = evalBlock fp xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hp : s.pc = x.pc := hpc x rfl
    cases xs with
    | nil =>
      have hf : fetch code x.pc = some x := by simpa only [blockOK,beq_iff_eq] using h
      simp only [List.length_cons,List.length_nil,run,evalBlock,step,hh,he,Bool.false_or,
        Bool.false_eq_true,if_false,hp,hf]
    | cons y ys =>
      have hs : fetch code x.pc = some x ∧ fallsThrough x.instruction = true ∧
          x.pc+x.length = y.pc ∧ blockOK code (y::ys) = true := by
        simpa only [blockOK,Bool.and_eq_true,beq_iff_eq,and_assoc] using h
      let t := execute fp x.instruction {s with pc := x.pc+x.length}
      have ht := execute_linear fp x.instruction {s with pc := x.pc+x.length} hs.2.1
      have hstep : step fp code s = t := by
        simp only [step,hh,he,Bool.false_or,Bool.false_eq_true,if_false,hp,hs.1]
        simp only [t, hh, he]
      rw [List.length_cons,run,hstep]
      change run fp code (y::ys).length t = evalBlock fp (y::ys) t
      apply ih t hs.2.2.2
      · intro z hz
        have hz' : y = z := Option.some.inj hz
        subst z
        exact ht.1.trans hs.2.2.1
      · exact ht.2.1.trans hh
      · exact ht.2.2.trans he

theorem evalBlock_reaches (fp : IEEEInstructions) (code : List Located) (xs : List Located)
    (s : State) (h : blockOK code xs = true)
    (hpc : ∀ x, xs.head? = some x → s.pc = x.pc)
    (hh : s.halted = false) (he : s.invalid = false) :
    Reaches fp code s (evalBlock fp xs s) :=
  ⟨xs.length,run_block fp code xs s h hpc hh he⟩

end Div3Machine
