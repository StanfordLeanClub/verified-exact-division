import Div3Machine.Contract
import Div3Machine.Counters

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

theorem body1 (fp : IEEEInstructions) (s : State) (a : ℕ)
    (hl : alive s) (hp : s.pc = 0x1cd) (hc : ScalarConstants s)
    (ha : address s (.indexed 6 0 4 0) = a) :
    ∃ t, Reaches fp program s t ∧ Fixed s t ∧ alive t ∧ ScalarConstants t ∧
      t.memory = s.memory ∧ t.g 0 = s.g 0 ∧ t.pc = 0x1c0 ∧
      t.trace = s.trace ++ [⟨false,a,4⟩] ∧
      decode (t.v 4 0) = reference (decode (read32 s.memory a)) := by
  let u := evalBlock fp b_guard1 s
  rcases guard1_effect fp s a ha hc with ⟨um,ug,ux,uv,up,ut⟩
  have bm := block_control_meta fp b_guard1 s (by decide +kernel)
  have ur : Reaches fp program s u := reaches_at fp b_guard1 s b_guard1_ok hp hl
  have ul : alive u := bm.2.mpr hl
  have uc : ScalarConstants u := scalar_constants_preserved fp b_guard1 s (by decide +kernel) hc
  cases hf : scalarTiny (read32 s.memory a) with
  | false =>
    have ue : u.pc = 0x1c0 := by simpa only [hf,Bool.false_eq_true,if_false] using up
    refine ⟨u,ur,bm.1,ul,uc,um,ug,ue,ut,?_⟩
    rw [uv,rawWord_value]
    exact tight_raw_correct _ (by rw [scalarTiny_eq] at hf; rw [hf]; decide)
  | true =>
    let t := evalBlock fp b_slow1 u
    have ue : u.pc = 0x1ef := by simpa only [hf,if_true] using up
    have tr := reaches_at fp b_slow1 u b_slow1_ok ue ul
    have tm := block_control_meta fp b_slow1 u (by decide +kernel)
    rcases slow1_effect fp u uc with ⟨mm,gg,vv,pp,tt⟩
    have tc := scalar_constants_preserved fp b_slow1 u (by decide +kernel) uc
    refine ⟨t,ur.trans tr,bm.1.trans tm.1,tm.2.mpr ul,tc,
      mm.trans um,(congrFun gg 0).trans ug,pp,tt.trans ut,?_⟩
    rw [vv,divWord_value,ux]

theorem step1 (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : ScalarConstants s) (hi : i < c.n) (hp : s.pc = 0x1cd) :
    ∃ t, Reaches fp program s t ∧ Inv c initial t (i+1) ∧ ScalarConstants t ∧
      t.pc = (if i+1=c.n then 0x1f5 else 0x1cd) := by
  have sa := arg.of_fixed inv.fixed
  have hs := indexed_address s 6 c.src i c.n 0 1 valid.src64 valid.n64 valid.srcBound (by omega) (by decide)
    (by decide) sa.src inv.index
  simp only [Nat.add_zero] at hs
  obtain ⟨u,ur,uf,ul,uc,um,ug,up,ut,uv⟩ := body1 fp s (c.src+4*i) inv.live hp hc hs
  have ua := sa.of_fixed uf
  have ui : u.g 0 = BitVec.ofNat 64 i := ug.trans inv.index
  have hd := indexed_address u 7 c.dst i c.n 0 1 valid.dst64 valid.n64 valid.dstBound (by omega) (by decide)
    (by decide) ua.dst ui
  simp only [Nat.add_zero] at hd
  let t := evalBlock fp b_store1 u
  have tr := reaches_at fp b_store1 u b_store1_ok up ul
  have tm := block_control_meta fp b_store1 u (by decide +kernel)
  rcases store1_effect fp u (c.dst+4*i) hd with ⟨teM,teI,teP,teT⟩
  have ti : t.g 0 = BitVec.ofNat 64 (i+1) := by
    calc
      t.g 0 = u.g 0+1 := teI
      _ = BitVec.ofNat 64 i+BitVec.ofNat 64 1 := congrArg (fun w : Reg64 => w+1) ui
      _ = _ := bv_add i 1
  have tp : Prefix initial.memory t.memory c.src c.dst c.n (i+1) := by
    rw [show t.memory = _ from teM,um]
    have h := prefix_advance_initial initial.memory s.memory c.src c.dst c.n i [u.v 4 0]
      valid.buffers (by simpa using (show i+1 ≤ c.n by omega)) inv.progress (by
        intro k hk
        have hk0 : k=0 := by simpa using hk
        subst k
        simpa only [List.getElem_cons_zero,Nat.add_zero,inv.progress.unread i (by omega) hi] using uv)
    simpa only [List.length_singleton,writeWords] using h
  have ts : Safe c t.trace := by
    rw [show t.trace = _ from teT,ut]
    apply safe_append (safe_append inv.safe (safe_read (chunk_readable _ _ _ _ _ i 1 0 4 (by omega) (by decide))))
    exact safe_write (chunk_writable _ _ i 1 0 4 (by omega) (by decide))
  have tc := scalar_constants_preserved fp b_store1 u (by decide +kernel) uc
  refine ⟨t,ur.trans tr,⟨tm.2.mpr ul,inv.fixed.trans (uf.trans tm.1),ti,tp,ts⟩,tc,?_⟩
  rw [show t.pc = _ from teP,ui,ua.n]
  change (if BitVec.ofNat 64 c.n == BitVec.ofNat 64 i+BitVec.ofNat 64 1 then _ else _) = _
  rw [bv_add,bv_beq _ _ valid.n64 (by have := valid.n64; omega)]
  by_cases he : c.n=i+1 <;> simp [he,eq_comm]

end Div3Machine
