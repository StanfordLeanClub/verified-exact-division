import Div3IEEE.Tight

namespace Div3Machine

abbrev Byte := BitVec 8
abbrev Word := BitVec 32
abbrev Memory := ℕ → Byte

def read32 (m : Memory) (a : ℕ) : Word := BitVec.ofNat 32
  ((m a).toNat + 256*(m (a+1)).toNat + 65536*(m (a+2)).toNat + 16777216*(m (a+3)).toNat)

def byteOf (w : Word) (i : ℕ) : Byte := BitVec.ofNat 8 (w.toNat / 256^i)

def write32 (m : Memory) (a : ℕ) (w : Word) : Memory :=
  fun p => if a ≤ p ∧ p < a+4 then byteOf w (p-a) else m p

theorem write32_outside (m : Memory) (a : ℕ) (w : Word) (p : ℕ)
    (h : p < a ∨ a+4 ≤ p) : write32 m a w p = m p := by
  simp only [write32]
  rw [if_neg (by omega)]

theorem read32_write32 (m : Memory) (a : ℕ) (w : Word) :
    read32 (write32 m a w) a = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [read32,write32]
  have h0 : a ≤ a ∧ a < a+4 := by omega
  have h1 : a ≤ a+1 ∧ a+1 < a+4 := by omega
  have h2 : a ≤ a+2 ∧ a+2 < a+4 := by omega
  have h3 : a ≤ a+3 ∧ a+3 < a+4 := by omega
  simp only [if_pos h0,if_pos h1,if_pos h2,if_pos h3,Nat.add_sub_cancel_left,Nat.sub_self]
  simp only [byteOf,BitVec.toNat_ofNat]
  norm_num only [Nat.reducePow,Nat.div_one]
  omega

theorem read32_congr (m m' : Memory) (a : ℕ)
    (h : ∀ p, a ≤ p → p < a+4 → m p = m' p) : read32 m a = read32 m' a := by
  simp only [read32]
  rw [h a (by omega) (by omega),h (a+1) (by omega) (by omega),
      h (a+2) (by omega) (by omega),h (a+3) (by omega) (by omega)]

def writeWords (m : Memory) (a : ℕ) : List Word → Memory
  | [] => m
  | w::ws => writeWords (write32 m a w) (a+4) ws

theorem writeWords_outside (m : Memory) (a : ℕ) (ws : List Word) (p : ℕ)
    (h : p < a ∨ a+4*ws.length ≤ p) : writeWords m a ws p = m p := by
  induction ws generalizing m a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons] at h
    rw [writeWords,ih _ _ (by omega),write32_outside _ _ _ _ (by omega)]

theorem read32_writeWords_outside (m : Memory) (a : ℕ) (ws : List Word) (b : ℕ)
    (h : b+4 ≤ a ∨ a+4*ws.length ≤ b) :
    read32 (writeWords m a ws) b = read32 m b := by
  apply read32_congr
  intro p hp hp'
  exact writeWords_outside _ _ _ _ (by omega)

theorem read32_writeWords (m : Memory) (a : ℕ) (ws : List Word) (i : ℕ)
    (hi : i < ws.length) : read32 (writeWords m a ws) (a+4*i) = ws[i] := by
  induction ws generalizing m a i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,writeWords,List.getElem_cons_zero]
      rw [read32_writeWords_outside _ _ _ _ (Or.inl (by omega)),read32_write32]
    | succ i =>
      simp only [writeWords,List.getElem_cons_succ]
      have he : a+4*(i+1) = (a+4)+4*i := by omega
      rw [he]
      exact ih _ _ i (by simpa using hi)

def readWords (m : Memory) (a n : ℕ) : List Word :=
  List.ofFn (fun i : Fin n => read32 m (a+4*i.val))

@[simp] theorem readWords_length (m : Memory) (a n : ℕ) : (readWords m a n).length = n := by
  simp [readWords]

def DisjointOrEqual (src dst n : ℕ) : Prop :=
  src = dst ∨ src+4*n ≤ dst ∨ dst+4*n ≤ src

/-- Address-side invariant for actual 4-byte and 32-byte accesses. -/
theorem access_in_bounds (base n i width : ℕ) (hi : i+width ≤ n)
    (hb : base+4*n ≤ 2^64) (k : ℕ) (hk : k < 4*width) :
    base ≤ base+4*i+k ∧ base+4*i+k < base+4*n ∧ base+4*i+k < 2^64 := by
  omega

theorem future_source_unchanged (m : Memory) (src dst n i : ℕ) (ws : List Word)
    (ha : DisjointOrEqual src dst n) (_hi : i+ws.length ≤ n)
    (j : ℕ) (hj : i+ws.length ≤ j) (hjn : j < n) :
    read32 (writeWords m (dst+4*i) ws) (src+4*j) = read32 m (src+4*j) := by
  apply read32_writeWords_outside
  rcases ha with h | h | h <;> omega

end Div3Machine
