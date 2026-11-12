import Div3Machine.Vector8
import Div3Machine.Contract
import Div3Machine.Counters

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

theorem body8 (fp : IEEEInstructions) (s : State) (a : ℕ)
    (hl : alive s) (hp : s.pc = 0x160) (hc : Constants s)
    (ha : address s (.indexed 6 0 4 0) = a) :
    ∃ t, Reaches fp program s t ∧ Fixed s t ∧ alive t ∧ Constants t ∧
      t.memory = s.memory ∧ t.g = s.g ∧ t.pc = 0x181 ∧
      t.trace = s.trace ++ [⟨false,a,32⟩] ∧
      (∀ j : Fin 8, decode (t.v 7 j) = reference (decode (readVec s.memory a j))) := by
  let u := evalBlock fp b_guard8 s
  have ug := guard8_effect fp s a ha hc
  have um := block_meta fp b_guard8 s (by decide +kernel)
  have ur : Reaches fp program s u := reaches_at fp b_guard8 s b_guard8_ok hp hl
  have ul : alive u := um.2.1.mpr hl
  have uc : Constants u := um.2.2 hc
  cases hf : all8 (fun j => compiledFast (readVec s.memory a j)) with
  | false =>
    let t := evalBlock fp b_slow8 u
    have ue : u.pc = 0x196 := by simpa only [hf,Bool.false_eq_true,if_false] using ug.2.2.2.1
    have tr := reaches_at fp b_slow8 u b_slow8_ok ue ul
    have tm := block_meta fp b_slow8 u (by decide +kernel)
    have te := slow8_effect fp u uc
    refine ⟨t,ur.trans tr,um.1.trans tm.1,tm.2.1.mpr ul,tm.2.2 uc,
      te.1.trans ug.1,te.2.1.trans ug.2.1,te.2.2.2.1,te.2.2.2.2.trans ug.2.2.2.2,?_⟩
    intro j
    rw [show t.v 7 = _ from te.2.2.1,divWord_value,show u.v 6 = _ from ug.2.2.1]
  | true =>
    let t := evalBlock fp b_fast8 u
    have ue : u.pc = 0x178 := by simpa only [hf,if_true] using ug.2.2.2.1
    have tr := reaches_at fp b_fast8 u b_fast8_ok ue ul
    have tm := block_meta fp b_fast8 u (by decide +kernel)
    have te := fast8_effect fp u uc
    refine ⟨t,ur.trans tr,um.1.trans tm.1,tm.2.1.mpr ul,tm.2.2 uc,
      te.1.trans ug.1,te.2.1.trans ug.2.1,te.2.2.2.1,te.2.2.2.2.trans ug.2.2.2.2,?_⟩
    intro j
    rw [show t.v 7 = _ from te.2.2.1,packedRaw_value,show u.v 6 = _ from ug.2.2.1]
    exact tight_raw_correct _ (by rw [guard8_safe s.memory a j hf]; decide)

end Div3Machine
