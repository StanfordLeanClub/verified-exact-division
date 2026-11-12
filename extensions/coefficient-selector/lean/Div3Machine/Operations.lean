import Div3Machine.Memory

namespace Div3Machine
open Div3IEEE ExactFDiv
set_option maxRecDepth 3000

/-- The value projection of the three hardware FP instruction specifications.
No compiler or whole-kernel correctness is assumed. NaN payloads are abstracted
by `decode`. This is the explicit ISA/IEEE boundary of the machine theorem. -/
structure IEEEInstructions where
  mul : Word → Word → Word
  fma : Word → Word → Word → Word
  div : Word → Word → Word
  mul_spec : ∀ a b, decode (mul a b) = ExactFDiv.mul round32 (decode a) (decode b)
  fma_spec : ∀ a b c, decode (fma a b c) = ExactFDiv.fma round32 (decode a) (decode b) (decode c)
  /-- Only the divisor used by this image; no premise about unused divisors. -/
  div_spec : ∀ a, decode (div a (0x40400000 : Word)) = reference (decode a)

def hiWord : Word := 0x3eaaaaaa
def loWord : Word := 0x32aaaaab
def threeWord : Word := 0x40400000

theorem literal_values : decode hiWord = .num hi ∧ decode loWord = .num lo ∧
    decode threeWord = .num 3 := by decide +kernel

def rawWord (fp : IEEEInstructions) (w : Word) := fp.fma w hiWord (fp.mul w loWord)
def divWord (fp : IEEEInstructions) (w : Word) := fp.div w threeWord

theorem rawWord_value (fp : IEEEInstructions) (w : Word) :
    decode (rawWord fp w) = raw (decode w) := by
  rw [rawWord,fp.fma_spec,fp.mul_spec,literal_values.1,literal_values.2.1]
  rfl

theorem divWord_value (fp : IEEEInstructions) (w : Word) :
    decode (divWord fp w) = reference (decode w) := by
  exact fp.div_spec w

def doubled (w : Word) : Word := w+w+BitVec.ofNat 32 0x7fffffff
def compiledFast (w : Word) : Bool := (BitVec.ofNat 32 0x9a7ffffe).slt (doubled w)

theorem twice_shift (w : Word) : w+w = w <<< (1:ℕ) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  congr 1
  omega

theorem compiledFast_eq (w : Word) : compiledFast w = !tightTiny w := by
  unfold compiledFast doubled tightTiny
  rw [twice_shift]
  simp only [BitVec.slt_eq_decide]
  have h0 : (BitVec.ofNat 32 0x9a7ffffe).toInt = -1702887426 := by decide +kernel
  have h1 : (BitVec.ofNat 32 0x9a7fffff).toInt = -1702887425 := by decide +kernel
  rw [h0,h1]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
  omega

def smin (a b : Word) : Word := if a.slt b then a else b

theorem smin_toInt (a b : Word) : (smin a b).toInt = min a.toInt b.toInt := by
  unfold smin
  simp only [BitVec.slt_eq_decide,decide_eq_true_eq]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (by omega)).symm

theorem smin_above (a b c : Word) : c.slt (smin a b) = (c.slt a && c.slt b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.slt_eq_decide,smin_toInt]

theorem compiled_four_guard (a b c d : Word) :
    (BitVec.ofNat 32 0x9a7ffffe).slt (smin (smin (doubled a) (doubled b))
      (smin (doubled c) (doubled d))) =
      ((!tightTiny a && !tightTiny b) && (!tightTiny c && !tightTiny d)) := by
  rw [smin_above,smin_above,smin_above]
  simp only [← compiledFast_eq,compiledFast]

def scalarTiny (w : Word) : Bool := ((w &&& 0x7fffffff)-1).ule 0x0d3ffffe

theorem scalarTiny_eq (w : Word) : scalarTiny w = tightTiny w := by
  have hm : (w &&& 0x7fffffff).toNat = w.toNat % 2147483648 := by
    rw [BitVec.toNat_and]
    change w.toNat &&& (2^31-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [tightTiny_bits]
  unfold scalarTiny
  rw [BitVec.ule_eq_decide,BitVec.toNat_sub,hm]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  norm_num only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  have h1 : (1 : Word).toNat = 1 := by decide +kernel
  have hc : (0x0d3ffffe : Word).toNat = 222298110 := by decide +kernel
  rw [h1,hc]
  have hlt : w.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  omega

abbrev Vec := Fin 8 → Word
def cmpMask (a b : Word) : Word := if b.slt a then 0xffffffff else 0
def ptestCF (a b : Vec) : Bool := decide (∀ i, (~~~a i &&& b i) = 0)
def all8 (f : Fin 8 → Bool) : Bool := decide (∀ i, f i = true)

theorem ptest_compare (f : Fin 8 → Bool) :
    ptestCF (fun i => if f i then 0xffffffff else 0) (fun _ => 0xffffffff) = all8 f := by
  have h (b : Bool) : (~~~(if b then (0xffffffff:Word) else 0) &&& 0xffffffff) = 0 ↔ b = true := by
    cases b <;> decide +kernel
  simp only [ptestCF,all8,h]

def wordResult (fp : IEEEInstructions) (slow : Bool) (w : Word) : Word :=
  if slow then divWord fp w else rawWord fp w

theorem wordResult_correct (fp : IEEEInstructions) (slow : Bool) (w : Word)
    (h : slow = false → tightTiny w = false) :
    decode (wordResult fp slow w) = reference (decode w) := by
  cases slow
  · simp only [wordResult,Bool.false_eq_true,if_false,rawWord_value]
    exact tight_raw_correct w (by rw [h rfl]; decide)
  · exact divWord_value fp w

end Div3Machine
