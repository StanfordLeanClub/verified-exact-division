import Div3Machine.Vector32
import Div3Machine.Body8Kernel
import Div3Machine.Counters

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

theorem body32 (fp : IEEEInstructions) (s : State) (a : ℕ)
    (hl : alive s) (hp : s.pc = 0x50) (hc : Constants s)
    (ha : ∀ off ∈ [0,32,64,96], address s (.indexed 6 0 4 off) = a+off) :
    ∃ t, Reaches fp program s t ∧ Fixed s t ∧ alive t ∧ Constants t ∧
      t.memory = s.memory ∧ t.g = s.g ∧ t.pc = 0xe0 ∧
      t.trace = s.trace ++ reads32 a ∧
      (∀ j : Fin 8, decode (t.v 8 j) = reference (decode (readVec s.memory a j))) ∧
      (∀ j : Fin 8, decode (t.v 10 j) = reference (decode (readVec s.memory (a+32) j))) ∧
      (∀ j : Fin 8, decode (t.v 9 j) = reference (decode (readVec s.memory (a+64) j))) ∧
      (∀ j : Fin 8, decode (t.v 7 j) = reference (decode (readVec s.memory (a+96) j))) := by
  let u := evalBlock fp b_guard32 s
  rcases guard32_effect fp s a ha hc with ⟨um,ug,u0,u1,u2,u3,up,ut⟩
  have bm := block_meta fp b_guard32 s (by decide +kernel)
  have ur : Reaches fp program s u := reaches_at fp b_guard32 s b_guard32_ok hp hl
  have ul : alive u := bm.2.1.mpr hl
  have uc : Constants u := bm.2.2 hc
  cases hf : fast32 s.memory a with
  | false =>
    let t := evalBlock fp b_slow32 u
    have ue : u.pc = 0x106 := by simpa only [hf,Bool.false_eq_true,if_false] using up
    have tr := reaches_at fp b_slow32 u b_slow32_ok ue ul
    have tm := block_meta fp b_slow32 u (by decide +kernel)
    rcases slow32_effect fp u uc with ⟨mm,gg,v0,v1,v2,v3,pp,tt⟩
    refine ⟨t,ur.trans tr,bm.1.trans tm.1,tm.2.1.mpr ul,tm.2.2 uc,
      mm.trans um,gg.trans ug,pp,tt.trans ut,?_,?_,?_,?_⟩
    · intro j; rw [v0,divWord_value,u0]
    · intro j; rw [v1,divWord_value,u1]
    · intro j; rw [v2,divWord_value,u2]
    · intro j; rw [v3,divWord_value,u3]
  | true =>
    let t := evalBlock fp b_fast32 u
    have ue : u.pc = 0xbc := by simpa only [hf,if_true] using up
    have tr := reaches_at fp b_fast32 u b_fast32_ok ue ul
    have tm := block_meta fp b_fast32 u (by decide +kernel)
    rcases fast32_effect fp u uc with ⟨mm,gg,v0,v1,v2,v3,pp,tt⟩
    refine ⟨t,ur.trans tr,bm.1.trans tm.1,tm.2.1.mpr ul,tm.2.2 uc,
      mm.trans um,gg.trans ug,pp,tt.trans ut,?_,?_,?_,?_⟩
    · intro j; rw [v0,packedRaw_value,u0]
      exact tight_raw_correct _ (by rw [(guard32_safe s.memory a j hf).1]; decide)
    · intro j; rw [v1,packedRaw_value,u1]
      exact tight_raw_correct _ (by rw [(guard32_safe s.memory a j hf).2.1]; decide)
    · intro j; rw [v2,packedRaw_value,u2]
      exact tight_raw_correct _ (by rw [(guard32_safe s.memory a j hf).2.2.1]; decide)
    · intro j; rw [v3,packedRaw_value,u3]
      exact tight_raw_correct _ (by rw [(guard32_safe s.memory a j hf).2.2.2]; decide)

theorem step32 (fp : IEEEInstructions) (c : Config) (initial s : State) (i q : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : Constants s) (hi : i+32 ≤ c.n) (hp : s.pc = 0x50)
    (hq : q+1 < 2^64) (hcount : s.g 1 = BitVec.ofNat 64 (q+1)) :
    ∃ t, Reaches fp program s t ∧ Inv c initial t (i+32) ∧ Constants t ∧
      t.g 1 = BitVec.ofNat 64 q ∧ t.pc = (if q=0 then 0x104 else 0x50) := by
  have sa := arg.of_fixed inv.fixed
  have hs : ∀ off ∈ [0,32,64,96], address s (.indexed 6 0 4 off) = (c.src+4*i)+off := by
    intro off ho
    have hlt : off < 128 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
    exact indexed_address s 6 c.src i c.n off 32 valid.src64 valid.n64 valid.srcBound hi (by decide)
      hlt sa.src inv.index
  obtain ⟨u,ur,uf,ul,uc,um,ug,up,ut,uv0,uv1,uv2,uv3⟩ := body32 fp s (c.src+4*i) inv.live hp hc hs
  have hd : ∀ off ∈ [0,32,64,96], address u (.indexed 7 0 4 off) = (c.dst+4*i)+off := by
    intro off ho
    have hlt : off < 128 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
    have h := indexed_address s 7 c.dst i c.n off 32 valid.dst64 valid.n64 valid.dstBound hi (by decide)
      hlt sa.dst inv.index
    simpa only [address,ug] using h
  let t := evalBlock fp b_store32 u
  have tr := reaches_at fp b_store32 u b_store32_ok up ul
  have tm := block_meta fp b_store32 u (by decide +kernel)
  rcases store32_effect fp u (c.dst+4*i) hd with ⟨teM,teI,teC,teP,teT⟩
  have ti : t.g 0 = BitVec.ofNat 64 (i+32) := by
    calc
      t.g 0 = u.g 0+BitVec.ofNat 64 32 := teI
      _ = BitVec.ofNat 64 i+BitVec.ofNat 64 32 := congrArg (fun w : Reg64 => w+BitVec.ofNat 64 32)
        ((congrFun ug 0).trans inv.index)
      _ = _ := bv_add i 32
  have hc0 : u.g 1-1 = BitVec.ofNat 64 q := by
    rw [ug,hcount,minus1 (q+1) hq (by omega)]
    rfl
  have tc : t.g 1 = BitVec.ofNat 64 q := teC.trans hc0
  have tp : Prefix initial.memory t.memory c.src c.dst c.n (i+32) := by
    rw [show t.memory = _ from teM,um]
    apply prefix_four _ _ _ _ _ _ _ _ _ _ valid.buffers hi inv.progress
    · intro j
      have he : c.src+4*i+4*j.val=c.src+4*(i+j.val) := by omega
      simpa only [readVec,he,inv.progress.unread (i+j.val) (by omega) (by have := j.isLt; omega)] using uv0 j
    · intro j
      have he : c.src+4*i+32+4*j.val=c.src+4*(i+8+j.val) := by omega
      simpa only [readVec,he,inv.progress.unread (i+8+j.val) (by omega) (by have := j.isLt; omega)] using uv1 j
    · intro j
      have he : c.src+4*i+64+4*j.val=c.src+4*(i+16+j.val) := by omega
      simpa only [readVec,he,inv.progress.unread (i+16+j.val) (by omega) (by have := j.isLt; omega)] using uv2 j
    · intro j
      have he : c.src+4*i+96+4*j.val=c.src+4*(i+24+j.val) := by omega
      simpa only [readVec,he,inv.progress.unread (i+24+j.val) (by omega) (by have := j.isLt; omega)] using uv3 j
  have ts : Safe c t.trace := by
    rw [show t.trace = _ from teT,ut]
    apply safe_append (safe_append inv.safe ?_) ?_
    · intro x hx
      simp only [reads32,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        first | exact chunk_readable _ _ _ _ _ i 32 0 32 hi (by decide)
              | exact chunk_readable _ _ _ _ _ i 32 32 32 hi (by decide)
              | exact chunk_readable _ _ _ _ _ i 32 64 32 hi (by decide)
              | exact chunk_readable _ _ _ _ _ i 32 96 32 hi (by decide)
    · intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl <;>
        first | exact chunk_writable _ _ i 32 0 32 hi (by decide)
              | exact chunk_writable _ _ i 32 32 32 hi (by decide)
              | exact chunk_writable _ _ i 32 64 32 hi (by decide)
              | exact chunk_writable _ _ i 32 96 32 hi (by decide)
  refine ⟨t,ur.trans tr,⟨tm.2.1.mpr ul,inv.fixed.trans (uf.trans tm.1),ti,tp,ts⟩,tm.2.2 uc,tc,?_⟩
  rw [show t.pc = _ from teP,hc0]
  change (if BitVec.ofNat 64 q == BitVec.ofNat 64 0 then _ else _) = _
  rw [bv_beq q 0 (by omega) (by decide)]
  simp only [decide_eq_true_eq]

end Div3Machine
