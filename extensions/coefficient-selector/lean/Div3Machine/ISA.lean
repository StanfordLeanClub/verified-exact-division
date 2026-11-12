import Div3Machine.Operations

namespace Div3Machine

abbrev Reg64 := BitVec 64

inductive Address where
  | indexed (base index scale displacement : ℕ)
  | image (offset : ℕ)
  deriving DecidableEq, Repr

inductive Condition where
  | below | aboveEqual | above | equal | notEqual
  deriving DecidableEq, Repr

/-- Only the instruction forms in the checked leaf function. Register numbers
are the architectural encodings (RAX=0, RCX=1, RDX=2, RSP=4, RSI=6, RDI=7).
Memory is byte-addressed; effective-address arithmetic wraps at 64 bits. -/
inductive Instruction where
  | cmpImm64 (reg : ℕ) (value : ℤ)
  | cmp64 (left right : ℕ)
  | mov64 (dst src : ℕ)
  | sub64 (dst src : ℕ)
  | addImm64 (dst : ℕ) (value : ℤ)
  | leaSub (dst src amount : ℕ)
  | shr64 (dst amount : ℕ)
  | inc64 (dst : ℕ)
  | dec64 (dst : ℕ)
  | zero32 (dst : ℕ)
  | and32 (dst : ℕ) (value : Word)
  | dec32 (dst : ℕ)
  | cmpImm32 (reg : ℕ) (value : Word)
  | wordToGpr (dst src : ℕ)
  | load (dst lanes : ℕ) (address : Address)
  | broadcast (dst : ℕ) (address : Address)
  | store (src lanes : ℕ) (address : Address)
  | addPacked (dst a b : ℕ)
  | minSigned (dst a b : ℕ)
  | compareSigned (dst a b : ℕ)
  | compareEqual (dst a b : ℕ)
  | mul (packed : Bool) (dst a b : ℕ)
  | fma231 (packed : Bool) (dst a b : ℕ)
  | div (packed : Bool) (dst a b : ℕ)
  | ptest (a b : ℕ)
  | branch (condition : Condition) (target : ℕ)
  | jump (target : ℕ)
  | zeroUpper
  | ret
  | nop
  deriving DecidableEq, Repr

structure Located where
  pc : ℕ
  length : ℕ
  instruction : Instruction
  deriving DecidableEq, Repr

structure Access where
  write : Bool
  address : ℕ
  bytes : ℕ
  deriving DecidableEq, Repr

structure State where
  g : ℕ → Reg64
  v : ℕ → Vec
  memory : Memory
  pc : ℕ
  imageBase : ℕ
  cf : Bool
  zf : Bool
  halted : Bool := false
  invalid : Bool := false
  trace : List Access := []

def address (s : State) : Address → ℕ
  | .indexed b i scale displacement =>
      ((s.g b).toNat + scale*(s.g i).toNat + displacement) % 2^64
  | .image offset => (s.imageBase+offset) % 2^64

def readVec (m : Memory) (a : ℕ) : Vec := fun i => read32 m (a+4*i.val)
def writeVec (m : Memory) (a : ℕ) (v : Vec) : Memory := writeWords m a (List.ofFn v)

def read64 (m : Memory) (a : ℕ) : Reg64 := BitVec.ofNat 64
  (∑ i : Fin 8, (m (a+i.val)).toNat * 256^i.val)

def setG (s : State) (r : ℕ) (w : Reg64) : State := {s with g := Function.update s.g r w}
def setV (s : State) (r : ℕ) (v : Vec) : State := {s with v := Function.update s.v r v}
def track (s : State) (write : Bool) (a width : ℕ) : State :=
  {s with trace := s.trace ++ [⟨write,a,width⟩]}

def condition (s : State) : Condition → Bool
  | .below => s.cf
  | .aboveEqual => !s.cf
  | .above => !s.cf && !s.zf
  | .equal => s.zf
  | .notEqual => !s.zf

def fpWrite (packed : Bool) (_old upper : Vec) (f : Fin 8 → Word) : Vec :=
  fun i => if packed then f i else if i.val = 0 then f i
    else if i.val < 4 then upper i else 0

/-- Value/byte projection of sequential user-mode x86 execution. Other status
flags and FP exception bits are deliberately omitted because this function does
not branch on them and its public contract excludes them. Memory faults are
excluded only by the proved access bounds and caller's mapping/permissions. -/
def execute (fp : IEEEInstructions) (op : Instruction) (s : State) : State :=
  match op with
  | .cmpImm64 r k => {s with cf := (s.g r).ult (BitVec.ofInt 64 k), zf := s.g r == BitVec.ofInt 64 k}
  | .cmp64 a b => {s with cf := (s.g a).ult (s.g b), zf := s.g a == s.g b}
  | .mov64 d a => setG s d (s.g a)
  | .sub64 d a =>
      let t := s.g d - s.g a
      {setG s d t with cf := (s.g d).ult (s.g a), zf := t == 0}
  | .addImm64 d k =>
      let t := s.g d + BitVec.ofInt 64 k
      {setG s d t with cf := t.ult (s.g d), zf := t == 0}
  | .leaSub d a k => setG s d (s.g a - BitVec.ofNat 64 k)
  | .shr64 d k =>
      let t := s.g d >>> k
      {setG s d t with cf := (s.g d).getLsbD (k-1), zf := t == 0}
  | .inc64 d => let t := s.g d+1; {setG s d t with zf := t == 0}
  | .dec64 d => let t := s.g d-1; {setG s d t with zf := t == 0}
  | .zero32 d => {setG s d 0 with cf := false,zf := true}
  | .and32 d w =>
      let t := (s.g d).setWidth 32 &&& w
      {setG s d (t.setWidth 64) with cf := false,zf := t == 0}
  | .dec32 d => let t := (s.g d).setWidth 32 - 1; {setG s d (t.setWidth 64) with zf := t == 0}
  | .cmpImm32 r w => {s with cf := ((s.g r).setWidth 32).ult w, zf := (s.g r).setWidth 32 == w}
  | .wordToGpr d a => setG s d ((s.v a 0).setWidth 64)
  | .load d lanes a =>
      let p := address s a
      setV (track s false p (4*lanes)) d (fun i => if i.val < lanes then read32 s.memory (p+4*i.val) else 0)
  | .broadcast d a =>
      let p := address s a
      setV (track s false p 4) d (fun _ => read32 s.memory p)
  | .store a lanes addr =>
      let p := address s addr
      {track s true p (4*lanes) with memory := writeWords s.memory p ((List.ofFn (s.v a)).take lanes)}
  | .addPacked d a b => setV s d (fun i => s.v a i+s.v b i)
  | .minSigned d a b => setV s d (fun i => smin (s.v a i) (s.v b i))
  | .compareSigned d a b => setV s d (fun i => cmpMask (s.v a i) (s.v b i))
  | .compareEqual d a b => setV s d (fun i => if s.v a i = s.v b i then 0xffffffff else 0)
  | .mul packed d a b => setV s d (fpWrite packed (s.v d) (s.v a) (fun i => fp.mul (s.v a i) (s.v b i)))
  | .fma231 packed d a b => setV s d (fpWrite packed (s.v d) (s.v d) (fun i => fp.fma (s.v a i) (s.v b i) (s.v d i)))
  | .div packed d a b => setV s d (fpWrite packed (s.v d) (s.v a) (fun i => fp.div (s.v a i) (s.v b i)))
  | .ptest a b => {s with cf := ptestCF (s.v a) (s.v b), zf := decide (∀ i, (s.v a i &&& s.v b i) = 0)}
  | .branch c t => if condition s c then {s with pc := t} else s
  | .jump t => {s with pc := t}
  | .zeroUpper => {s with v := fun r i => if i.val < 4 then s.v r i else 0}
  | .ret =>
      let a := (s.g 4).toNat
      {track (setG s 4 (s.g 4+8)) false a 8 with pc := (read64 s.memory a).toNat,halted := true}
  | .nop => s

def fetch (code : List Located) (pc : ℕ) : Option Located := code.find? (fun x => x.pc == pc)

def step (fp : IEEEInstructions) (code : List Located) (s : State) : State :=
  if s.halted || s.invalid then s else
  match fetch code s.pc with
  | none => {s with invalid := true}
  | some x => execute fp x.instruction {s with pc := s.pc+x.length}

def run (fp : IEEEInstructions) (code : List Located) : ℕ → State → State
  | 0,s => s
  | n+1,s => run fp code n (step fp code s)

theorem run_add (fp : IEEEInstructions) (code : List Located) (a b : ℕ) (s : State) :
    run fp code (a+b) s = run fp code b (run fp code a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,run]
  | succ a ih => simpa only [Nat.succ_add,run] using ih (step fp code s)

def Reaches (fp : IEEEInstructions) (code : List Located) (s t : State) : Prop :=
  ∃ k, run fp code k s = t

theorem Reaches.trans {fp : IEEEInstructions} {code : List Located} {s t u : State}
    (h : Reaches fp code s t) (h' : Reaches fp code t u) : Reaches fp code s u := by
  obtain ⟨k,rfl⟩ := h
  obtain ⟨k',hk'⟩ := h'
  exact ⟨k+k',by rw [run_add,hk']⟩

end Div3Machine
