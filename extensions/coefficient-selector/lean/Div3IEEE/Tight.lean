import Div3IEEE.Array
import Div3IEEE.Bridge

namespace Div3IEEE
open ExactFDiv

/-- Smallest binary32 threshold satisfying the exact normal-low-product bound.
It is 25% lower than the previous power-of-two threshold. -/
def tightThreshold : ℚ := 3*(2:ℚ)^(-102:ℤ)

theorem tight_low_guard : minNormal 24 (-149) ≤ tightThreshold*lo := by
  norm_num [minNormal,tightThreshold,lo]

theorem predecessor_low_fails :
    magnitude 26 4194303 * lo < minNormal 24 (-149) := by
  norm_num [magnitude,significand,quantum,lo,minNormal]

theorem tight_le_old : tightThreshold ≤ threshold := by norm_num [tightThreshold,threshold]

theorem fast_tight_correct {x : ℚ} (hx : ValidNum 24 (-149) 104 x)
    (hg : tightThreshold ≤ |x|) : raw (.num x) = reference (.num x) := by
  apply CoefficientSelector.arbitrary_pair_guarded (p:=24) (by norm_num) (by norm_num)
    hx (h:=hi) (l:=lo) (y:=3) (T:=tightThreshold)
  · simpa only [abs_of_pos lo_pos] using lo_le_one
  · simpa only [abs_of_pos hi_pos,abs_of_pos lo_pos] using three_lo_le_hi
  · norm_num [lo]
  · simpa only [abs_of_pos lo_pos] using tight_low_guard
  · exact hg
  · exact unbounded hx.1 hx.2.1.isFloat

theorem tight_bits_imply_range {e f : ℕ} (he : e < 255) (hf : f < 8388608)
    (hg : 222298112 ≤ e*8388608+f) : tightThreshold ≤ magnitude e f := by
  by_cases heq : e = 26
  · subst e
    have hc : (12582912:ℚ) ≤ (8388608+f:ℕ) := by
      exact_mod_cast (show 12582912 ≤ 8388608+f by omega)
    have hm := mul_le_mul_of_nonneg_right hc (two_zpow_pos (-124)).le
    norm_num [magnitude,significand,quantum,tightThreshold] at hm ⊢
    linarith
  · have h27 : 27 ≤ e := by omega
    have hge : threshold ≤ magnitude e f := by
      apply le_of_not_gt
      intro hlt
      have hh := (magnitude_lt_threshold he hf).mp hlt
      omega
    exact tight_le_old.trans hge

def tightTiny (w : BitVec 32) : Bool :=
  ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff).slt (BitVec.ofNat 32 0x9a7fffff)

theorem tightTiny_bits (w : BitVec 32) : tightTiny w =
    decide (0 < w.toNat % 2147483648 ∧ w.toNat % 2147483648 < 222298112) := by
  unfold tightTiny
  rw [BitVec.slt_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hm : w.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have ht : ((w <<< (1:ℕ)) + BitVec.ofNat 32 0x7fffffff).toNat =
      (2*(w.toNat % 2147483648)+2147483647)%4294967296 := by
    rw [BitVec.toNat_add,shifted_magnitude]
    rfl
  have hc : (BitVec.ofNat 32 0x9a7fffff).toInt = (-1702887425:ℤ) := by decide +kernel
  rw [hc,BitVec.toInt_eq_toNat_cond,ht]
  norm_num only [Nat.reducePow]
  split_ifs <;> omega

theorem tight_raw_correct (w : BitVec 32) (hg : tightTiny w ≠ true) :
    raw (decode w) = reference (decode w) := by
  have hbits := fields_identity w
  have hng : ¬(0 < w.toNat % 2147483648 ∧ w.toNat % 2147483648 < 222298112) := by
    intro h
    exact hg ((tightTiny_bits w).trans (decide_eq_true_eq.mpr h))
  have he : exponent w < 256 := Nat.mod_lt _ (by norm_num)
  have hf : fraction w < 8388608 := Nat.mod_lt _ (by norm_num)
  have hv := decode_valid w
  unfold decode decodeFields at hv ⊢
  by_cases hi : exponent w = 255
  · by_cases hz : fraction w = 0
    · simp only [if_pos hi,if_pos hz]
      exact raw_special (by intro v h; cases h)
    · simp only [if_pos hi,if_neg hz]
      exact raw_special (by intro v h; cases h)
  by_cases hz : exponent w = 0 ∧ fraction w = 0
  · simp only [if_neg hi,if_pos hz]
    exact raw_special (by intro v h; cases h)
  simp only [if_neg hi,if_neg hz] at hv ⊢
  apply fast_tight_correct hv
  rw [abs_withSign w.msb (magnitude_nonneg _ _)]
  apply tight_bits_imply_range (by omega) hf
  omega

/-- Direct slow arm: the old helper's second mask and branch are unnecessary. -/
def tightBlock (ws : List (BitVec 32)) : List IEEE :=
  if ws.any tightTiny then ws.map (fun w => reference (decode w))
  else ws.map (fun w => raw (decode w))

theorem tightBlock_correct (ws : List (BitVec 32)) :
    tightBlock ws = ws.map (fun w => reference (decode w)) := by
  unfold tightBlock
  split_ifs with ht
  · rfl
  · apply List.map_congr_left
    intro w hw
    exact tight_raw_correct w (fun h => ht (List.any_eq_true.mpr ⟨w,hw,h⟩))

def tightScalar (w : BitVec 32) : IEEE :=
  if tightTiny w then reference (decode w) else raw (decode w)

theorem tightScalar_correct (w : BitVec 32) : tightScalar w = reference (decode w) := by
  unfold tightScalar
  split_ifs with h
  · rfl
  · exact tight_raw_correct w h

def tightArray (ws : List (BitVec 32)) : List IEEE :=
  executeArray tightBlock tightScalar ws

theorem tightArray_correct (ws : List (BitVec 32)) :
    tightArray ws = ws.map (fun w => reference (decode w)) :=
  executeArray_correct tightBlock tightScalar tightBlock_correct tightScalar_correct ws

theorem tight_flags_subset (w : BitVec 32) (h : tightTiny w = true) : nativeTiny w = true := by
  rw [tightTiny_bits] at h
  rw [nativeTiny_bits]
  simp only [decide_eq_true_eq] at h ⊢
  omega

theorem tight_threshold_encoding : decode (BitVec.ofNat 32 0x0d400000) = .num tightThreshold := by
  decide +kernel

theorem newly_fast : tightTiny (BitVec.ofNat 32 0x0d400000) = false ∧
    nativeTiny (BitVec.ofNat 32 0x0d400000) = true := by decide +kernel

end Div3IEEE
