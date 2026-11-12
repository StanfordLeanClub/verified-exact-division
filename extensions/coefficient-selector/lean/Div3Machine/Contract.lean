import Div3Machine.Control
import Div3Machine.ChunkMemory

namespace Div3Machine
open Div3IEEE

structure Config where
  src : ℕ
  dst : ℕ
  n : ℕ
  image : ℕ
  stack : ℕ

structure Valid (c : Config) : Prop where
  src64 : c.src < 2^64
  dst64 : c.dst < 2^64
  n64 : c.n < 2^64
  srcBound : c.src+4*c.n ≤ 2^64
  dstBound : c.dst+4*c.n ≤ 2^64
  imageBound : c.image+532 ≤ 2^64
  stackBound : c.stack+8 < 2^64
  buffers : DisjointOrEqual c.src c.dst c.n
  imageSeparate : c.dst+4*c.n ≤ c.image ∨ c.image+532 ≤ c.dst
  stackSeparate : c.dst+4*c.n ≤ c.stack ∨ c.stack+8 ≤ c.dst

structure Args (c : Config) (s : State) : Prop where
  src : s.g 6 = BitVec.ofNat 64 c.src
  dst : s.g 7 = BitVec.ofNat 64 c.dst
  n : s.g 2 = BitVec.ofNat 64 c.n
  stack : s.g 4 = BitVec.ofNat 64 c.stack
  image : s.imageBase = c.image

def Safe (c : Config) (trace : List Access) : Prop := ∀ x ∈ trace,
  if x.write then Writable c.dst c.n x.address x.bytes
  else Readable c.src c.n c.image 532 c.stack x.address x.bytes

structure Inv (c : Config) (initial s : State) (i : ℕ) : Prop where
  live : alive s
  fixed : Fixed initial s
  index : s.g 0 = BitVec.ofNat 64 i
  progress : Prefix initial.memory s.memory c.src c.dst c.n i
  safe : Safe c s.trace

theorem Inv.unchanged {c : Config} {initial s t : State} {i : ℕ}
    (h : Inv c initial s i) (hf : Fixed s t) (hl : alive t)
    (hg : t.g 0 = s.g 0) (hm : t.memory = s.memory) (ht : Safe c t.trace) :
    Inv c initial t i := by
  exact ⟨hl,h.fixed.trans hf,hg.trans h.index,by rw [hm]; exact h.progress,ht⟩

theorem Args.of_fixed {c : Config} {s t : State} (a : Args c s) (h : Fixed s t) : Args c t := by
  exact ⟨(h.regs 6 (by decide) (by decide)).trans a.src,
    (h.regs 7 (by decide) (by decide)).trans a.dst,(h.regs 2 (by decide) (by decide)).trans a.n,
    (h.regs 4 (by decide) (by decide)).trans a.stack,h.base.trans a.image⟩

theorem indexed_address (s : State) (baseReg base i n off k : ℕ)
    (hb : base < 2^64) (hn : n < 2^64) (he : base+4*n ≤ 2^64)
    (hi : i+k ≤ n) (hk : 0 < k) (ho : off < 4*k)
    (hg : s.g baseReg = BitVec.ofNat 64 base) (hidx : s.g 0 = BitVec.ofNat 64 i) :
    address s (.indexed baseReg 0 4 off) = base+4*i+off := by
  simp only [address,hg,hidx,bv_nat _ hb,bv_nat i (by omega : i<2^64)]
  apply Nat.mod_eq_of_lt
  omega

theorem Inv.image_constants {c : Config} {initial s : State} {i : ℕ}
    (h : Inv c initial s i) (a : Args c initial) (v : Valid c) (hi : i ≤ c.n)
    (hl : Loaded initial.memory c.image) : ImageConstants s := by
  have arg := a.of_fixed h.fixed
  apply loaded_constants
  · rw [arg.image]
    exact prefix_loaded _ _ _ _ _ _ _ hi h.progress hl v.imageSeparate
  · rw [arg.image]; exact v.imageBound

theorem safe_append {c : Config} {xs ys : List Access} (h : Safe c xs) (h' : Safe c ys) :
    Safe c (xs++ys) := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact h x hx
  · exact h' x hx

theorem safe_read {c : Config} {a w : ℕ} (h : Readable c.src c.n c.image 532 c.stack a w) :
    Safe c [⟨false,a,w⟩] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  exact h

theorem safe_write {c : Config} {a w : ℕ} (h : Writable c.dst c.n a w) :
    Safe c [⟨true,a,w⟩] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  exact h

theorem safe_constants {c : Config} {s : State} (a : Args c s) (v : Valid c) :
    Safe c (constantReads s) := by
  have ha (off : ℕ) (ho : off < 532) : address s (.image off) = c.image+off := by
    simp only [address,a.image]
    exact Nat.mod_eq_of_lt (by have := v.imageBound; omega)
  intro x hx
  simp only [constantReads,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;>
    simp only [Bool.false_eq_true,if_false,ha 512 (by decide),ha 516 (by decide),
      ha 520 (by decide),ha 524 (by decide),ha 528 (by decide)] <;>
    right <;> left <;> constructor <;> omega

end Div3Machine
