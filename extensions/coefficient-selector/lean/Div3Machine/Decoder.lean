import Div3Machine.ISA

namespace Div3Machine

/-- Fail-closed decoder for the x86-64/VEX encodings used by this one artifact.
It reads opcode, register, SIB, immediate, and relative-displacement bits.
It does not consume disassembler text or trust compiler annotations. -/
def octet (image : List ℕ) (p : ℕ) : ℕ := (image[p]?).getD 0
def le32 (image : List ℕ) (p : ℕ) : ℕ :=
  octet image p+256*octet image (p+1)+65536*octet image (p+2)+16777216*octet image (p+3)
def signed8 (x : ℕ) : ℤ := if x < 128 then x else (x:ℤ)-256
def signed32 (x : ℕ) : ℤ := if x < 2147483648 then x else (x:ℤ)-4294967296

inductive RM where
  | reg (r : ℕ)
  | mem (a : Address)
  deriving DecidableEq, Repr

def decodeRM (image : List ℕ) (p extB extX : ℕ) : Option (RM × ℕ) := do
  let m := octet image p
  let mode := m/64
  let rm := m%8
  if mode = 3 then return (.reg (rm+8*extB),1)
  if mode = 0 ∧ rm = 5 then
    let target : ℤ := (p+5:ℕ)+signed32 (le32 image (p+1))
    if target < 0 then none else return (.mem (.image target.toNat),5)
  else if rm = 4 then
    let sib := octet image (p+1)
    let base := sib%8+8*extB
    let idx := sib/8%8+8*extX
    if (mode = 0 ∧ sib%8 = 5) ∨ idx = 4 then none else
    let displacement : ℤ := if mode = 0 then 0 else if mode = 1 then
      signed8 (octet image (p+2)) else signed32 (le32 image (p+2))
    if displacement < 0 then none else
    return (.mem (.indexed base idx (2^(sib/64)) displacement.toNat),
      if mode = 0 then 2 else if mode = 1 then 3 else 6)
  else none

def finishDecode (image : List ℕ) (pc len : ℕ) (op : Instruction) : Option Located :=
  if pc+len ≤ image.length then some ⟨pc,len,op⟩ else none

def decodeVex (image : List ℕ) (pc : ℕ) : Option Located := do
  let b0 := octet image pc
  let b1 := octet image (pc+1)
  let b2 := if b0 = 0xc5 then b1 else octet image (pc+2)
  let pfx := if b0 = 0xc5 then 2 else 3
  let map := if b0 = 0xc5 then 1 else b1%32
  let extR := 1-b1/128
  let extX := if b0 = 0xc5 then 0 else 1-b1/64%2
  let extB := if b0 = 0xc5 then 0 else 1-b1/32%2
  let w := if b0 = 0xc5 then 0 else b2/128
  let a := 15-b2/8%16
  let packed := b2/4%2 = 1
  let pp := b2%4
  let opcode := octet image (pc+pfx)
  let m := octet image (pc+pfx+1)
  let d := m/8%8+8*extR
  if w ≠ 0 then none else
  let (rm,n) ← decodeRM image (pc+pfx+1) extB extX
  let len := pfx+1+n
  let done := finishDecode image pc len
  match rm with
  | .mem addr =>
    if a ≠ 0 then none else
    if map = 2 ∧ pp = 1 ∧ packed ∧ (opcode = 0x58 ∨ opcode = 0x18) then
      done (.broadcast d addr)
    else if map = 1 ∧ packed ∧ ((opcode = 0x10 ∧ pp = 0) ∨ (opcode = 0x6f ∧ pp = 2)) then
      done (.load d 8 addr)
    else if map = 1 ∧ packed ∧ opcode = 0x11 ∧ pp = 0 then done (.store d 8 addr)
    else if map = 1 ∧ ¬packed ∧ ((opcode = 0x10 ∧ pp = 2) ∨ (opcode = 0x6e ∧ pp = 1)) then
      done (.load d 1 addr)
    else if map = 1 ∧ ¬packed ∧ opcode = 0x11 ∧ pp = 2 then done (.store d 1 addr)
    else none
  | .reg b =>
    if map = 1 ∧ packed ∧ pp = 1 ∧ opcode = 0xfe then done (.addPacked d a b)
    else if map = 2 ∧ packed ∧ pp = 1 ∧ opcode = 0x39 then done (.minSigned d a b)
    else if map = 1 ∧ packed ∧ pp = 1 ∧ opcode = 0x66 then done (.compareSigned d a b)
    else if map = 1 ∧ packed ∧ pp = 1 ∧ opcode = 0x76 then done (.compareEqual d a b)
    else if map = 2 ∧ packed ∧ pp = 1 ∧ a = 0 ∧ opcode = 0x17 then done (.ptest d b)
    else if map = 1 ∧ ((packed ∧ pp = 0) ∨ (¬packed ∧ pp = 2)) ∧ opcode = 0x59 then
      done (.mul (decide packed) d a b)
    else if map = 1 ∧ ((packed ∧ pp = 0) ∨ (¬packed ∧ pp = 2)) ∧ opcode = 0x5e then
      done (.div (decide packed) d a b)
    else if map = 2 ∧ pp = 1 ∧ ((packed ∧ opcode = 0xb8) ∨ (¬packed ∧ opcode = 0xb9)) then
      done (.fma231 (decide packed) d a b)
    else if map = 1 ∧ ¬packed ∧ pp = 1 ∧ a = 0 ∧ opcode = 0x7e then done (.wordToGpr b d)
    else none

def relativeTarget (pc len : ℕ) (displacement : ℤ) : Option ℕ :=
  let target := (pc+len:ℕ)+displacement
  if target < 0 then none else some target.toNat

def decodeAt (image : List ℕ) (pc : ℕ) : Option Located := do
  let b := fun i => octet image (pc+i)
  let done := finishDecode image pc
  if b 0 = 0xc3 then done 1 .ret
  else if (image.drop pc).take 3 == [0xc5,0xf8,0x77] then done 3 .zeroUpper
  else if b 0 = 0xc5 ∨ b 0 = 0xc4 then decodeVex image pc
  else if (image.drop pc).take 8 == [0x0f,0x1f,0x84,0,0,0,0,0] then done 8 .nop
  else if (image.drop pc).take 9 == [0x66,0x0f,0x1f,0x84,0,0,0,0,0] then done 9 .nop
  else if (image.drop pc).take 5 == [0x0f,0x1f,0x44,0,0] then done 5 .nop
  else if b 0 = 0xeb then
    let t ← relativeTarget pc 2 (signed8 (b 1)); done 2 (.jump t)
  else if b 0 = 0x72 ∨ b 0 = 0x73 ∨ b 0 = 0x74 ∨ b 0 = 0x75 ∨ b 0 = 0x77 then
    let t ← relativeTarget pc 2 (signed8 (b 1))
    let c := if b 0 = 0x72 then Condition.below else if b 0 = 0x73 then .aboveEqual
      else if b 0 = 0x74 then .equal else if b 0 = 0x75 then .notEqual else .above
    done 2 (.branch c t)
  else if b 0 = 0x0f ∧ (b 1 = 0x82 ∨ b 1 = 0x85) then
    let t ← relativeTarget pc 6 (signed32 (le32 image (pc+2)))
    done 6 (.branch (if b 1 = 0x82 then .below else .notEqual) t)
  else if b 0 = 0x48 then
    let m := b 2
    let d := m%8
    let a := m/8%8
    if b 1 = 0x8d ∧ m/64 = 1 then
      let k := signed8 (b 3)
      if k ≤ 0 then done 4 (.leaSub a d (-k).toNat) else none
    else if m/64 ≠ 3 then none else
    if b 1 = 0x83 ∧ a = 7 then done 4 (.cmpImm64 d (signed8 (b 3)))
    else if b 1 = 0x83 ∧ a = 0 then done 4 (.addImm64 d (signed8 (b 3)))
    else if b 1 = 0xc1 ∧ a = 5 ∧ 0 < b 3 ∧ b 3 < 64 then done 4 (.shr64 d (b 3))
    else if b 1 = 0xff ∧ a = 0 then done 3 (.inc64 d)
    else if b 1 = 0xff ∧ a = 1 then done 3 (.dec64 d)
    else if b 1 = 0x89 then done 3 (.mov64 d a)
    else if b 1 = 0x29 then done 3 (.sub64 d a)
    else if b 1 = 0x39 then done 3 (.cmp64 d a)
    else none
  else if b 0 = 0x31 ∧ b 1 / 64 = 3 ∧ b 1 % 8 = b 1 / 8 % 8 then
    done 2 (.zero32 (b 1 % 8))
  else if b 0 = 0x81 ∧ b 1 / 64 = 3 then
    let d := b 1 % 8
    let w := BitVec.ofNat 32 (le32 image (pc+2))
    if b 1 / 8 % 8 = 4 then done 6 (.and32 d w)
    else if b 1 / 8 % 8 = 7 then done 6 (.cmpImm32 d w) else none
  else if b 0 = 0xff ∧ b 1 / 64 = 3 ∧ b 1 / 8 % 8 = 1 then done 2 (.dec32 (b 1 % 8))
  else none

def decodeAux (image : List ℕ) (textLength : ℕ) : ℕ → ℕ → Option (List Located)
  | 0,pc => if pc = textLength then some [] else none
  | fuel+1,pc => do
      if pc = textLength then return []
      let x ← decodeAt image pc
      if x.length = 0 ∨ textLength < pc+x.length then none else
      let rest ← decodeAux image textLength fuel (pc+x.length)
      return x::rest

def decodeText (image : List ℕ) (textLength : ℕ) : Option (List Located) :=
  if image.all (fun b => b < 256) then decodeAux image textLength textLength 0 else none

end Div3Machine
