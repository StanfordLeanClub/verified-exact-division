import Div3Machine.Support

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

def imageMemory : Memory := fun j => BitVec.ofNat 8 (imageBytes[j]?.getD 0)

def Loaded (m : Memory) (base : ℕ) : Prop :=
  ∀ j, j < 532 → m (base+j) = imageMemory j

def ImageConstants (s : State) : Prop :=
  read32 s.memory (address s (.image 512)) = BitVec.ofNat 32 0x7fffffff ∧
  read32 s.memory (address s (.image 516)) = BitVec.ofNat 32 0x9a7ffffe ∧
  read32 s.memory (address s (.image 520)) = threeWord ∧
  read32 s.memory (address s (.image 524)) = loWord ∧
  read32 s.memory (address s (.image 528)) = hiWord

theorem image_literals :
    read32 imageMemory 512 = BitVec.ofNat 32 0x7fffffff ∧
    read32 imageMemory 516 = BitVec.ofNat 32 0x9a7ffffe ∧
    read32 imageMemory 520 = threeWord ∧ read32 imageMemory 524 = loWord ∧
    read32 imageMemory 528 = hiWord := by decide +kernel

theorem loaded_word (m : Memory) (base off : ℕ) (h : Loaded m base) (ho : off+4 ≤ 532) :
    read32 m (base+off) = read32 imageMemory off := by
  unfold read32
  have h0 := h off (by omega)
  have h1 := h (off+1) (by omega)
  have h2 := h (off+2) (by omega)
  have h3 := h (off+3) (by omega)
  simp only [Nat.add_assoc,h0,h1,h2,h3]

theorem loaded_constants (s : State) (h : Loaded s.memory s.imageBase)
    (hb : s.imageBase+532 ≤ 2^64) : ImageConstants s := by
  have ha (off : ℕ) (ho : off < 532) : address s (.image off) = s.imageBase+off := by
    exact Nat.mod_eq_of_lt (by omega)
  unfold ImageConstants
  rw [ha 512 (by decide),ha 516 (by decide),ha 520 (by decide),ha 524 (by decide),ha 528 (by decide)]
  simp only [loaded_word _ _ _ h (by decide : 512+4 ≤ 532),
    loaded_word _ _ _ h (by decide : 516+4 ≤ 532),loaded_word _ _ _ h (by decide : 520+4 ≤ 532),
    loaded_word _ _ _ h (by decide : 524+4 ≤ 532),loaded_word _ _ _ h (by decide : 528+4 ≤ 532)]
  exact image_literals

theorem prefix_loaded (initial current : Memory) (src dst n i base : ℕ)
    (hi : i ≤ n) (h : Prefix initial current src dst n i) (hl : Loaded initial base)
    (hd : dst+4*n ≤ base ∨ base+532 ≤ dst) : Loaded current base := by
  intro j hj
  rw [h.frame (base+j) (by omega)]
  exact hl j hj

end Div3Machine
