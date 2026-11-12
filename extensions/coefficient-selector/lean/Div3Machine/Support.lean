import Div3Machine.Blocks
import Div3Machine.Arithmetic
import Div3Machine.Invariant

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

def alive (s : State) : Prop := s.halted = false ∧ s.invalid = false

def gDest : Instruction → Option ℕ
  | .mov64 d _ | .sub64 d _ | .addImm64 d _ | .leaSub d _ _ | .shr64 d _ |
    .inc64 d | .dec64 d | .zero32 d | .and32 d _ | .dec32 d | .wordToGpr d _ => some d
  | .ret => some 4
  | _ => none

def vDest : Instruction → Option ℕ
  | .load d _ _ | .broadcast d _ | .addPacked d _ _ | .minSigned d _ _ |
    .compareSigned d _ _ | .compareEqual d _ _ | .mul _ d _ _ |
    .fma231 _ d _ _ | .div _ d _ _ => some d
  | _ => none

theorem execute_g (fp : IEEEInstructions) (op : Instruction) (s : State) (r : ℕ)
    (h : gDest op ≠ some r) : (execute fp op s).g r = s.g r := by
  cases op <;> simp_all [gDest,execute,setG,setV,track,Function.update_apply]
  all_goals first | (intro he; exact False.elim (h he.symm)) | (split <;> rfl)

theorem execute_v (fp : IEEEInstructions) (op : Instruction) (s : State) (r : ℕ)
    (h : vDest op ≠ some r) (hz : op ≠ .zeroUpper) :
    (execute fp op s).v r = s.v r := by
  cases op <;> simp_all [vDest,execute,setG,setV,track,Function.update_apply]
  all_goals first | (intro he; exact False.elim (h he.symm)) | (split <;> rfl)

theorem execute_base (fp : IEEEInstructions) (op : Instruction) (s : State) :
    (execute fp op s).imageBase = s.imageBase := by
  cases op <;> simp [execute,setG,setV,track]
  split <;> rfl

theorem execute_alive (fp : IEEEInstructions) (op : Instruction) (s : State)
    (h : op ≠ .ret) : alive (execute fp op s) ↔ alive s := by
  cases op <;> simp_all [alive,execute,setG,setV,track]
  split <;> rfl

theorem block_g (fp : IEEEInstructions) (xs : List Located) (s : State) (r : ℕ)
    (h : ∀ x ∈ xs, gDest x.instruction ≠ some r) :
    (evalBlock fp xs s).g r = s.g r := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [evalBlock,ih _ (by simpa using (fun y hy => h y (List.mem_cons_of_mem _ hy)))]
    exact execute_g fp _ _ r (h x (by simp))

theorem block_v (fp : IEEEInstructions) (xs : List Located) (s : State) (r : ℕ)
    (h : ∀ x ∈ xs, vDest x.instruction ≠ some r ∧ x.instruction ≠ .zeroUpper) :
    (evalBlock fp xs s).v r = s.v r := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [evalBlock,ih _ (by simpa using (fun y hy => h y (List.mem_cons_of_mem _ hy)))]
    exact execute_v fp _ _ r (h x (by simp)).1 (h x (by simp)).2

theorem block_base (fp : IEEEInstructions) (xs : List Located) (s : State) :
    (evalBlock fp xs s).imageBase = s.imageBase := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [evalBlock,ih,execute_base]

theorem block_alive (fp : IEEEInstructions) (xs : List Located) (s : State)
    (h : ∀ x ∈ xs, x.instruction ≠ .ret) :
    alive (evalBlock fp xs s) ↔ alive s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [evalBlock,ih _ (by simpa using (fun y hy => h y (List.mem_cons_of_mem _ hy)))]
    exact execute_alive fp _ _ (h x (by simp))

theorem reaches_block (fp : IEEEInstructions) (xs : List Located) (s : State)
    (hc : blockOK program xs = true) (hp : ∀ x, xs.head? = some x → s.pc = x.pc)
    (ha : alive s) : Reaches fp program s (evalBlock fp xs s) :=
  evalBlock_reaches fp program xs s hc hp ha.1 ha.2

theorem reaches_at (fp : IEEEInstructions) (xs : List Located) (s : State)
    (hc : blockOK program xs = true)
    (hp : s.pc = (xs.head?.map Located.pc).getD 0) (ha : alive s) :
    Reaches fp program s (evalBlock fp xs s) := by
  apply reaches_block fp xs s hc _ ha
  intro x hx
  simpa only [hx,Option.map_some,Option.getD_some] using hp

def Constants (s : State) : Prop :=
    s.v 0 = (fun _ => BitVec.ofNat 32 0x7fffffff) ∧
    s.v 1 = (fun _ => BitVec.ofNat 32 0x9a7ffffe) ∧
    s.v 2 = (fun _ => 0xffffffff) ∧
    s.v 3 = (fun _ => threeWord) ∧
    s.v 4 = (fun _ => loWord) ∧
    s.v 5 = (fun _ => hiWord)

def scratchOnly (op : Instruction) : Bool :=
  match gDest op with
  | none => true
  | some r => r == 0 || r == 1

def keepsConstants (op : Instruction) : Bool :=
  op != .zeroUpper && match vDest op with
    | none => true
    | some r => decide (6 ≤ r)

def blockMeta (xs : List Located) : Bool :=
  xs.all (fun x => scratchOnly x.instruction && x.instruction != .ret && keepsConstants x.instruction)

def controlMeta (xs : List Located) : Bool := xs.all (fun x => scratchOnly x.instruction)

structure Fixed (s t : State) : Prop where
  regs : ∀ r, r ≠ 0 → r ≠ 1 → t.g r = s.g r
  base : t.imageBase = s.imageBase

theorem Fixed.trans {s t u : State} (h : Fixed s t) (h' : Fixed t u) : Fixed s u := by
  exact ⟨fun r h0 h1 => (h'.regs r h0 h1).trans (h.regs r h0 h1),h'.base.trans h.base⟩

theorem block_control_meta (fp : IEEEInstructions) (xs : List Located) (s : State)
    (h : controlMeta xs = true) :
    Fixed s (evalBlock fp xs s) ∧ (alive (evalBlock fp xs s) ↔ alive s) := by
  have hm : ∀ x ∈ xs, scratchOnly x.instruction = true := by simpa [controlMeta] using h
  have hg : ∀ r, r ≠ 0 → r ≠ 1 → ∀ x ∈ xs, gDest x.instruction ≠ some r := by
    intro r h0 h1 x hx he
    have := hm x hx
    simp [scratchOnly,he,h0,h1] at this
  have hr : ∀ x ∈ xs, x.instruction ≠ .ret := by
    intro x hx he
    have := hm x hx
    simp [scratchOnly,he,gDest] at this
  exact ⟨⟨fun r h0 h1 => block_g fp xs s r (hg r h0 h1),block_base fp xs s⟩,
    block_alive fp xs s hr⟩

theorem block_meta (fp : IEEEInstructions) (xs : List Located) (s : State)
    (h : blockMeta xs = true) :
    Fixed s (evalBlock fp xs s) ∧ (alive (evalBlock fp xs s) ↔ alive s) ∧
    (Constants s → Constants (evalBlock fp xs s)) := by
  have hm : ∀ x ∈ xs, scratchOnly x.instruction = true ∧ x.instruction ≠ .ret ∧
      keepsConstants x.instruction = true := by simpa [blockMeta,and_assoc] using h
  have hg : ∀ r, r ≠ 0 → r ≠ 1 → ∀ x ∈ xs, gDest x.instruction ≠ some r := by
    intro r h0 h1 x hx he
    have := (hm x hx).1
    simp [scratchOnly,he,h0,h1] at this
  have hv : ∀ r, r < 6 → ∀ x ∈ xs, vDest x.instruction ≠ some r ∧ x.instruction ≠ .zeroUpper := by
    intro r hr x hx
    have hh := (hm x hx).2.2
    simp only [keepsConstants,Bool.and_eq_true,bne_iff_ne] at hh
    refine ⟨?_,hh.1⟩
    intro he
    rw [he] at hh
    simp only [decide_eq_true_eq] at hh
    omega
  refine ⟨⟨fun r h0 h1 => block_g fp xs s r (hg r h0 h1),block_base fp xs s⟩,
    block_alive fp xs s (fun x hx => (hm x hx).2.1),?_⟩
  unfold Constants
  simp only [block_v fp xs s 0 (hv 0 (by decide)),block_v fp xs s 1 (hv 1 (by decide)),
    block_v fp xs s 2 (hv 2 (by decide)),block_v fp xs s 3 (hv 3 (by decide)),
    block_v fp xs s 4 (hv 4 (by decide)),block_v fp xs s 5 (hv 5 (by decide)),imp_self]

end Div3Machine
