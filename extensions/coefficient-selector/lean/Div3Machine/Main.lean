import Div3Machine.Phases

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

structure Precondition (c : Config) (initial : State) : Prop where
  valid : Valid c
  args : Args c initial
  loaded : Loaded initial.memory c.image
  entry : initial.pc=0
  running : alive initial
  emptyTrace : initial.trace=[]

structure Postcondition (c : Config) (initial final : State) : Prop where
  halted : final.halted=true
  valid : final.invalid=false
  returned : final.pc=(read64 initial.memory c.stack).toNat
  stack : final.g 4=BitVec.ofNat 64 (c.stack+8)
  preserved : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 4 → final.g r=initial.g r
  values : ∀ j, j < c.n → decode (read32 final.memory (c.dst+4*j)) =
    reference (decode (read32 initial.memory (c.src+4*j)))
  frame : ∀ p, p < c.dst ∨ c.dst+4*c.n ≤ p → final.memory p=initial.memory p
  accesses : Safe c final.trace
  loaded : Loaded final.memory c.image

theorem read64_congr (m m' : Memory) (a : ℕ) (h : ∀ k, k<8 → m (a+k)=m' (a+k)) :
    read64 m a=read64 m' a := by
  unfold read64
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [h j.val j.isLt]

/-- Total correctness of the exact decoded 505-byte code / 532-byte image.
The premise `fp` specifies only primitive ISA FP instructions. The theorem
does not assume correctness of any array, compiler, load/store, loop or guard. -/
theorem machine_correct (fp : IEEEInstructions) (c : Config) (initial : State)
    (pre : Precondition c initial) :
    ∃ final, Reaches fp program initial final ∧ Postcondition c initial final := by
  obtain ⟨s,i,sr,si,hi,_h32,sp⟩ := initial_phase fp c initial pre.valid pre.args pre.loaded
    pre.entry pre.running pre.emptyTrace
  obtain ⟨u,j,ur,ui,hj,_h8,up⟩ := vector_phase fp c initial s i pre.valid pre.args pre.loaded si hi sp
  obtain ⟨v,vr,vi,vp⟩ := scalar_phase fp c initial u j pre.valid pre.args pre.loaded ui hj up
  let final := evalBlock fp b_exit v
  have fr := reaches_at fp b_exit v b_exit_ok vp vi.live
  have arg := pre.args.of_fixed vi.fixed
  rcases return_effect fp v with ⟨fm,fp',fh,fi,fs,fg,ft⟩
  have stackNat : (v.g 4).toNat=c.stack := by
    rw [arg.stack,bv_nat _ (by have := pre.valid.stackBound; omega)]
  have stackMem : read64 v.memory c.stack=read64 initial.memory c.stack := by
    apply read64_congr
    intro k hk
    apply vi.progress.frame
    have := pre.valid.stackSeparate
    omega
  refine ⟨final,sr.trans (ur.trans (vr.trans fr)),?_⟩
  constructor
  · exact fh
  · exact fi.trans vi.live.2
  · rw [show final.pc = _ from fp',stackNat,stackMem]
  · calc
      final.g 4 = v.g 4+8 := fs
      _ = BitVec.ofNat 64 c.stack+BitVec.ofNat 64 8 := congrArg (fun w : Reg64 => w+8) arg.stack
      _ = _ := bv_add c.stack 8
  · intro r h0 h1 h4
    exact (fg r h4).trans (vi.fixed.regs r h0 h1)
  · intro k hk
    rw [show final.memory = _ from fm]
    exact vi.progress.processed k hk
  · intro p hp
    rw [show final.memory = _ from fm]
    exact vi.progress.frame p hp
  · rw [show final.trace = _ from ft,stackNat]
    apply safe_append vi.safe
    apply safe_read
    right; right; exact ⟨le_refl _,le_refl _⟩
  · rw [show final.memory = _ from fm]
    exact prefix_loaded _ _ _ _ _ _ _ (le_refl _) vi.progress pre.loaded pre.valid.imageSeparate

theorem instruction_fetch_bounds : ∀ x ∈ program, 0<x.length ∧ x.pc+x.length ≤ 505 := by
  have h : program.all (fun x => decide (0<x.length ∧ x.pc+x.length ≤ 505)) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h

/-- Interpreting the range theorem with actual caller-supplied permissions.
Each byte touched by any recorded load/store belongs to its permitted region. -/
theorem memory_permissions (c : Config) (trace : List Access) (h : Safe c trace)
    (canRead canWrite : ℕ → Prop)
    (hr : ∀ p, (c.src ≤ p ∧ p<c.src+4*c.n) ∨ (c.image ≤ p ∧ p<c.image+532) ∨
      (c.stack ≤ p ∧ p<c.stack+8) → canRead p)
    (hw : ∀ p, c.dst ≤ p → p<c.dst+4*c.n → canWrite p) :
    ∀ x ∈ trace, ∀ k, k<x.bytes → if x.write then canWrite (x.address+k) else canRead (x.address+k) := by
  intro x hx k hk
  have hs := h x hx
  cases he : x.write
  · simp only [he,Bool.false_eq_true,if_false] at hs ⊢
    apply hr
    rcases hs with hs|hs|hs
    · left; omega
    · right; left; omega
    · right; right; omega
  · simp only [he,if_true] at hs ⊢
    exact hw _ (by rcases hs with ⟨h1,h2⟩; omega) (by rcases hs with ⟨h1,h2⟩; omega)

end Div3Machine
