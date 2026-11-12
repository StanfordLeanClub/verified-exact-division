import Div3Machine.Operations

namespace Div3Machine
open Div3IEEE

/-- A byte-level loop invariant: the completed prefix has the correct values,
unread source words retain their initial bits, and every other byte is framed. -/
structure Prefix (initial current : Memory) (src dst n i : ℕ) : Prop where
  processed : ∀ j, j < i → decode (read32 current (dst+4*j)) = reference (decode (read32 initial (src+4*j)))
  unread : ∀ j, i ≤ j → j < n → read32 current (src+4*j) = read32 initial (src+4*j)
  frame : ∀ p, p < dst ∨ dst+4*i ≤ p → current p = initial p

theorem prefix_zero (m : Memory) (src dst n : ℕ) : Prefix m m src dst n 0 := by
  constructor
  · intro j hj; omega
  · intros; rfl
  · intros; rfl

theorem prefix_advance (initial current : Memory) (src dst n i : ℕ) (ws : List Word)
    (ha : DisjointOrEqual src dst n) (hi : i+ws.length ≤ n)
    (inv : Prefix initial current src dst n i)
    (values : ∀ k (hk : k < ws.length), decode ws[k] =
      reference (decode (read32 current (src+4*(i+k))))) :
    Prefix initial (writeWords current (dst+4*i) ws) src dst n (i+ws.length) := by
  constructor
  · intro j hj
    by_cases hji : j < i
    · rw [read32_writeWords_outside _ _ _ _ (Or.inl (by omega))]
      exact inv.processed j hji
    · have hk : j-i < ws.length := by omega
      have he : dst+4*j = (dst+4*i)+4*(j-i) := by omega
      rw [he,read32_writeWords _ _ _ _ hk]
      have hv := values (j-i) hk
      have hij : i+(j-i) = j := by omega
      rw [hij,inv.unread j (by omega) (by omega)] at hv
      exact hv
  · intro j hj hjn
    rw [future_source_unchanged _ _ _ _ _ _ ha hi j hj hjn]
    exact inv.unread j (by omega) hjn
  · intro p hp
    rw [writeWords_outside _ _ _ _ (by omega)]
    exact inv.frame p (by omega)

theorem prefix_finished (initial current : Memory) (src dst n : ℕ)
    (h : Prefix initial current src dst n n) :
    (∀ j, j < n → decode (read32 current (dst+4*j)) = reference (decode (read32 initial (src+4*j)))) ∧
    (∀ p, p < dst ∨ dst+4*n ≤ p → current p = initial p) :=
  ⟨h.processed,h.frame⟩

theorem writeWords_append (m : Memory) (a : ℕ) (xs ys : List Word) :
    writeWords m a (xs++ys) = writeWords (writeWords m a xs) (a+4*xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [writeWords]
  | cons x xs ih =>
    simp only [List.cons_append,writeWords,List.length_cons]
    rw [ih]
    congr 1
    omega

def Readable (src n imageBase imageLength stack : ℕ) (a width : ℕ) : Prop :=
  (src ≤ a ∧ a+width ≤ src+4*n) ∨
  (imageBase ≤ a ∧ a+width ≤ imageBase+imageLength) ∨
  (stack ≤ a ∧ a+width ≤ stack+8)

def Writable (dst n : ℕ) (a width : ℕ) : Prop := dst ≤ a ∧ a+width ≤ dst+4*n

theorem chunk_readable (src n imageBase imageLength stack i width offset bytes : ℕ)
    (hi : i+width ≤ n) (ho : offset+bytes ≤ 4*width) :
    Readable src n imageBase imageLength stack (src+4*i+offset) bytes := by
  left; omega

theorem chunk_writable (dst n i width offset bytes : ℕ)
    (hi : i+width ≤ n) (ho : offset+bytes ≤ 4*width) :
    Writable dst n (dst+4*i+offset) bytes := by
  constructor <;> omega

theorem effective_address (base n i offset : ℕ) (hb : base+4*n ≤ 2^64)
    (hi : i < n) (ho : offset < 4*(n-i)) :
    (base+4*i+offset)%2^64 = base+4*i+offset := by
  apply Nat.mod_eq_of_lt
  omega

end Div3Machine
