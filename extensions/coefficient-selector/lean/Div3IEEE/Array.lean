import Div3IEEE.Guard

namespace Div3IEEE
open ExactFDiv

/-- OR reduction of all-ones/zero comparison masks, sufficient for testz.
Flattening lanes changes neither whether any vector mask is nonzero nor its branch. -/
def combinedMask (flags : List Bool) : BitVec 32 :=
  flags.foldr (fun b r => (if b then BitVec.ofNat 32 0xffffffff else 0) ||| r) 0

theorem combinedMask_eq (flags : List Bool) : combinedMask flags =
    if flags.any id then BitVec.ofNat 32 0xffffffff else 0 := by
  induction flags with
  | nil => rfl
  | cons b bs ih =>
    change (if b then BitVec.ofNat 32 0xffffffff else 0) ||| combinedMask bs = _
    rw [ih]
    cases b <;> cases h : bs.any id <;> simp [h]

theorem combinedMask_zero (flags : List Bool) : combinedMask flags = 0 ↔ flags.any id = false := by
  rw [combinedMask_eq]
  cases flags.any id <;> decide

/-- AVX2 ORs corresponding lanes across vectors, then testz checks all 256 bits.
Each lane is a 32-bit comparison mask, so this models that exact reduction order. -/
def laneReduction (blocks : List (Fin 8 → Bool)) (i : Fin 8) : BitVec 32 :=
  combinedMask (blocks.map (fun b => b i))

theorem simd_testz_iff (blocks : List (Fin 8 → Bool)) :
    (∀ i, laneReduction blocks i = 0) ↔
      (blocks.flatMap List.ofFn).any id = false := by
  constructor
  · intro hz
    apply List.any_eq_false.mpr
    intro b hb
    obtain ⟨f,hf,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    have hall := List.any_eq_false.mp ((combinedMask_zero _).mp (hz i))
    exact hall _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · intro hn i
    apply (combinedMask_zero _).mpr
    apply List.any_eq_false.mpr
    intro b hb
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hb
    apply (List.any_eq_false.mp hn)
    exact List.mem_flatMap.mpr ⟨f,hf,List.mem_ofFn.mpr ⟨i,rfl⟩⟩

/-- The original P4Z block control flow, including the cold helper's second test.
The same-sign path has no separate zero or infinity repair. -/
def nativeBlock (ws : List (BitVec 32)) : List IEEE :=
  if ws.any nativeTiny then
    if ws.any coldTiny then ws.map (fun w => reference (decode w))
    else ws.map (fun w => raw (decode w))
  else ws.map (fun w => raw (decode w))

theorem nativeBlock_correct (ws : List (BitVec 32)) :
    nativeBlock ws = ws.map (fun w => reference (decode w)) := by
  have heq : coldTiny = nativeTiny := funext coldTiny_eq
  unfold nativeBlock
  rw [heq]
  by_cases ht : ws.any nativeTiny = true
  · simp [ht]
  · rw [if_neg ht]
    apply List.map_congr_left
    intro w hw
    have hn : nativeTiny w ≠ true := by
      intro h
      exact ht (List.any_eq_true.mpr ⟨w,hw,h⟩)
    have hc := nativeGuarded_correct w
    simpa only [nativeGuarded,if_neg hn] using hc

/-- Full loop shape: 32-element unrolled blocks, then 8-element vectors, then
scalar tails. List concatenation models result order, not pointer memory safety. -/
def nativeArray (ws : List (BitVec 32)) : List IEEE :=
  if 32 ≤ ws.length then nativeBlock (ws.take 32) ++ nativeArray (ws.drop 32)
  else if 8 ≤ ws.length then nativeBlock (ws.take 8) ++ nativeArray (ws.drop 8)
  else ws.map (fun w => scalar (decode w))
termination_by ws.length
decreasing_by all_goals simp only [List.length_drop]; omega

theorem nativeArray_correct (ws : List (BitVec 32)) :
    nativeArray ws = ws.map (fun w => reference (decode w)) := by
  rw [nativeArray]
  split_ifs with h32 h8
  · rw [nativeBlock_correct,nativeArray_correct (ws.drop 32)]
    rw [← List.map_append,List.take_append_drop]
  · rw [nativeBlock_correct,nativeArray_correct (ws.drop 8)]
    rw [← List.map_append,List.take_append_drop]
  · apply List.map_congr_left
    intro w _
    exact scalar_correct (decode w) (decode_valid w)
termination_by ws.length
decreasing_by all_goals simp only [List.length_drop]; omega

theorem nativeArray_length (ws : List (BitVec 32)) : (nativeArray ws).length = ws.length := by
  rw [nativeArray_correct,List.length_map]

/-- The loop is reusable for any certified block and scalar executors. -/
def executeArray (block : List (BitVec 32) → List IEEE) (tail : BitVec 32 → IEEE)
    (ws : List (BitVec 32)) : List IEEE :=
  if 32 ≤ ws.length then block (ws.take 32) ++ executeArray block tail (ws.drop 32)
  else if 8 ≤ ws.length then block (ws.take 8) ++ executeArray block tail (ws.drop 8)
  else ws.map tail
termination_by ws.length
decreasing_by all_goals simp only [List.length_drop]; omega

theorem executeArray_correct (block : List (BitVec 32) → List IEEE) (tail : BitVec 32 → IEEE)
    (hb : ∀ ws, block ws = ws.map (fun w => reference (decode w)))
    (ht : ∀ w, tail w = reference (decode w)) (ws : List (BitVec 32)) :
    executeArray block tail ws = ws.map (fun w => reference (decode w)) := by
  rw [executeArray]
  split_ifs with h32 h8
  · rw [hb,executeArray_correct block tail hb ht (ws.drop 32)]
    rw [← List.map_append,List.take_append_drop]
  · rw [hb,executeArray_correct block tail hb ht (ws.drop 8)]
    rw [← List.map_append,List.take_append_drop]
  · exact List.map_congr_left (fun w _ => ht w)
termination_by ws.length
decreasing_by all_goals simp only [List.length_drop]; omega

end Div3IEEE
