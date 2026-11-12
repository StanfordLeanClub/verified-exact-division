import Div3Machine.Program
import Div3Machine.Linear

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

def b_enter : List Located := [
  ⟨0x0,4,.cmpImm64 2 (32)⟩,
  ⟨0x4,6,.branch .below 280⟩
]
theorem b_enter_ok : blockOK program b_enter = true := by decide +kernel

def b_setup32 : List Located := [
  ⟨0xa,4,.leaSub 1 2 32⟩,
  ⟨0xe,4,.shr64 1 5⟩,
  ⟨0x12,3,.inc64 1⟩,
  ⟨0x15,9,.broadcast 0 (.image 512)⟩,
  ⟨0x1e,9,.broadcast 1 (.image 516)⟩,
  ⟨0x27,2,.zero32 0⟩,
  ⟨0x29,4,.compareEqual 2 2 2⟩,
  ⟨0x2d,9,.broadcast 3 (.image 520)⟩,
  ⟨0x36,9,.broadcast 4 (.image 524)⟩,
  ⟨0x3f,9,.broadcast 5 (.image 528)⟩,
  ⟨0x48,8,.nop⟩
]
theorem b_setup32_ok : blockOK program b_setup32 = true := by decide +kernel

def b_guard32 : List Located := [
  ⟨0x50,5,.load 10 8 (.indexed 6 0 4 0)⟩,
  ⟨0x55,6,.load 7 8 (.indexed 6 0 4 64)⟩,
  ⟨0x5b,6,.load 9 8 (.indexed 6 0 4 32)⟩,
  ⟨0x61,6,.load 6 8 (.indexed 6 0 4 96)⟩,
  ⟨0x67,5,.load 8 8 (.indexed 6 0 4 0)⟩,
  ⟨0x6c,6,.load 11 8 (.indexed 6 0 4 32)⟩,
  ⟨0x72,6,.load 12 8 (.indexed 6 0 4 64)⟩,
  ⟨0x78,5,.addPacked 8 8 8⟩,
  ⟨0x7d,4,.addPacked 8 8 0⟩,
  ⟨0x81,5,.addPacked 11 11 11⟩,
  ⟨0x86,4,.addPacked 11 11 0⟩,
  ⟨0x8a,5,.minSigned 8 11 8⟩,
  ⟨0x8f,5,.addPacked 11 12 12⟩,
  ⟨0x94,4,.addPacked 11 11 0⟩,
  ⟨0x98,6,.load 12 8 (.indexed 6 0 4 96)⟩,
  ⟨0x9e,5,.addPacked 12 12 12⟩,
  ⟨0xa3,4,.addPacked 12 12 0⟩,
  ⟨0xa7,5,.minSigned 11 11 12⟩,
  ⟨0xac,5,.minSigned 8 8 11⟩,
  ⟨0xb1,4,.compareSigned 8 8 1⟩,
  ⟨0xb5,5,.ptest 8 2⟩,
  ⟨0xba,2,.branch .aboveEqual 262⟩
]
theorem b_guard32_ok : blockOK program b_guard32 = true := by decide +kernel

def b_fast32 : List Located := [
  ⟨0xbc,4,.mul true 8 10 4⟩,
  ⟨0xc0,5,.fma231 true 8 5 10⟩,
  ⟨0xc5,4,.mul true 10 9 4⟩,
  ⟨0xc9,5,.fma231 true 10 5 9⟩,
  ⟨0xce,4,.mul true 9 7 4⟩,
  ⟨0xd2,5,.fma231 true 9 5 7⟩,
  ⟨0xd7,4,.mul true 7 6 4⟩,
  ⟨0xdb,5,.fma231 true 7 5 6⟩
]
theorem b_fast32_ok : blockOK program b_fast32 = true := by decide +kernel

def b_store32 : List Located := [
  ⟨0xe0,5,.store 8 8 (.indexed 7 0 4 0)⟩,
  ⟨0xe5,6,.store 10 8 (.indexed 7 0 4 32)⟩,
  ⟨0xeb,6,.store 9 8 (.indexed 7 0 4 64)⟩,
  ⟨0xf1,6,.store 7 8 (.indexed 7 0 4 96)⟩,
  ⟨0xf7,4,.addImm64 0 (32)⟩,
  ⟨0xfb,3,.dec64 1⟩,
  ⟨0xfe,6,.branch .notEqual 80⟩
]
theorem b_store32_ok : blockOK program b_store32 = true := by decide +kernel

def b_exit32 : List Located := [
  ⟨0x104,2,.jump 282⟩
]
theorem b_exit32_ok : blockOK program b_exit32 = true := by decide +kernel

def b_slow32 : List Located := [
  ⟨0x106,4,.div true 8 10 3⟩,
  ⟨0x10a,4,.div true 10 9 3⟩,
  ⟨0x10e,4,.div true 9 7 3⟩,
  ⟨0x112,4,.div true 7 6 3⟩,
  ⟨0x116,2,.jump 224⟩
]
theorem b_slow32_ok : blockOK program b_slow32 = true := by decide +kernel

def b_skip32 : List Located := [
  ⟨0x118,2,.zero32 0⟩
]
theorem b_skip32_ok : blockOK program b_skip32 = true := by decide +kernel

def b_check8 : List Located := [
  ⟨0x11a,3,.mov64 1 2⟩,
  ⟨0x11d,3,.sub64 1 0⟩,
  ⟨0x120,4,.cmpImm64 1 (8)⟩,
  ⟨0x124,2,.branch .below 412⟩
]
theorem b_check8_ok : blockOK program b_check8 = true := by decide +kernel

def b_setup8 : List Located := [
  ⟨0x126,9,.broadcast 0 (.image 512)⟩,
  ⟨0x12f,9,.broadcast 1 (.image 516)⟩,
  ⟨0x138,4,.compareEqual 2 2 2⟩,
  ⟨0x13c,9,.broadcast 3 (.image 520)⟩,
  ⟨0x145,9,.broadcast 4 (.image 524)⟩,
  ⟨0x14e,9,.broadcast 5 (.image 528)⟩,
  ⟨0x157,9,.nop⟩
]
theorem b_setup8_ok : blockOK program b_setup8 = true := by decide +kernel

def b_guard8 : List Located := [
  ⟨0x160,5,.load 6 8 (.indexed 6 0 4 0)⟩,
  ⟨0x165,4,.addPacked 7 6 6⟩,
  ⟨0x169,4,.addPacked 7 7 0⟩,
  ⟨0x16d,4,.compareSigned 7 7 1⟩,
  ⟨0x171,5,.ptest 7 2⟩,
  ⟨0x176,2,.branch .aboveEqual 406⟩
]
theorem b_guard8_ok : blockOK program b_guard8 = true := by decide +kernel

def b_fast8 : List Located := [
  ⟨0x178,4,.mul true 7 6 4⟩,
  ⟨0x17c,5,.fma231 true 7 5 6⟩
]
theorem b_fast8_ok : blockOK program b_fast8 = true := by decide +kernel

def b_store8 : List Located := [
  ⟨0x181,5,.store 7 8 (.indexed 7 0 4 0)⟩,
  ⟨0x186,4,.addImm64 0 (8)⟩,
  ⟨0x18a,4,.addImm64 1 (-8)⟩,
  ⟨0x18e,4,.cmpImm64 1 (7)⟩,
  ⟨0x192,2,.branch .above 352⟩
]
theorem b_store8_ok : blockOK program b_store8 = true := by decide +kernel

def b_exit8 : List Located := [
  ⟨0x194,2,.jump 412⟩
]
theorem b_exit8_ok : blockOK program b_exit8 = true := by decide +kernel

def b_slow8 : List Located := [
  ⟨0x196,4,.div true 7 6 3⟩,
  ⟨0x19a,2,.jump 385⟩
]
theorem b_slow8_ok : blockOK program b_slow8 = true := by decide +kernel

def b_check1 : List Located := [
  ⟨0x19c,3,.cmp64 0 2⟩,
  ⟨0x19f,2,.branch .aboveEqual 501⟩
]
theorem b_check1_ok : blockOK program b_check1 = true := by decide +kernel

def b_setup1 : List Located := [
  ⟨0x1a1,8,.load 0 1 (.image 524)⟩,
  ⟨0x1a9,8,.load 1 1 (.image 528)⟩,
  ⟨0x1b1,8,.load 2 1 (.image 520)⟩,
  ⟨0x1b9,2,.jump 461⟩
]
theorem b_setup1_ok : blockOK program b_setup1 = true := by decide +kernel

def b_store1 : List Located := [
  ⟨0x1c0,5,.store 4 1 (.indexed 7 0 4 0)⟩,
  ⟨0x1c5,3,.inc64 0⟩,
  ⟨0x1c8,3,.cmp64 2 0⟩,
  ⟨0x1cb,2,.branch .equal 501⟩
]
theorem b_store1_ok : blockOK program b_store1 = true := by decide +kernel

def b_guard1 : List Located := [
  ⟨0x1cd,5,.load 3 1 (.indexed 6 0 4 0)⟩,
  ⟨0x1d2,4,.wordToGpr 1 3⟩,
  ⟨0x1d6,6,.and32 1 (BitVec.ofNat 32 2147483647)⟩,
  ⟨0x1dc,2,.dec32 1⟩,
  ⟨0x1de,4,.mul false 4 3 0⟩,
  ⟨0x1e2,5,.fma231 false 4 3 1⟩,
  ⟨0x1e7,6,.cmpImm32 1 (BitVec.ofNat 32 222298110)⟩,
  ⟨0x1ed,2,.branch .above 448⟩
]
theorem b_guard1_ok : blockOK program b_guard1 = true := by decide +kernel

def b_slow1 : List Located := [
  ⟨0x1ef,4,.div false 4 3 2⟩,
  ⟨0x1f3,2,.jump 448⟩
]
theorem b_slow1_ok : blockOK program b_slow1 = true := by decide +kernel

def b_exit : List Located := [
  ⟨0x1f5,3,.zeroUpper⟩,
  ⟨0x1f8,1,.ret⟩
]
theorem b_exit_ok : blockOK program b_exit = true := by decide +kernel

end Div3Machine
