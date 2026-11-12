import Div3Machine.Body8Kernel

namespace Div3Machine
open Div3IEEE
set_option maxRecDepth 6000
set_option maxHeartbeats 200000

theorem step8 (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : Constants s) (hi : i+8 ≤ c.n) (hp : s.pc = 0x160)
    (hcount : s.g 1 = BitVec.ofNat 64 (c.n-i)) :
    ∃ t, Reaches fp program s t ∧ Inv c initial t (i+8) ∧ Constants t ∧
      t.g 1 = BitVec.ofNat 64 (c.n-(i+8)) ∧
      t.pc = (if i+16 ≤ c.n then 0x160 else 0x194) := by
  have sa := arg.of_fixed inv.fixed
  have hs := indexed_address s 6 c.src i c.n 0 8 valid.src64 valid.n64 valid.srcBound hi (by decide)
    (by decide) sa.src inv.index
  simp only [Nat.add_zero] at hs
  obtain ⟨u,ur,uf,ul,uc,um,ug,up,ut,uv⟩ := body8 fp s (c.src+4*i) inv.live hp hc hs
  have hd := indexed_address s 7 c.dst i c.n 0 8 valid.dst64 valid.n64 valid.dstBound hi (by decide)
    (by decide) sa.dst inv.index
  simp only [Nat.add_zero] at hd
  have ud : address u (.indexed 7 0 4 0) = c.dst+4*i := by simpa only [address,ug] using hd
  generalize ht : evalBlock fp b_store8 u = t
  have tr := reaches_at fp b_store8 u b_store8_ok up ul
  have tm := block_meta fp b_store8 u (by decide +kernel)
  have te := store8_effect fp u (c.dst+4*i) ud
  dsimp only at te
  rw [ht] at tr tm te
  rcases te with ⟨teM,teI,teC,teP,teT⟩
  have ti : t.g 0 = BitVec.ofNat 64 (i+8) := by
    calc
      t.g 0 = u.g 0+BitVec.ofNat 64 8 := teI
      _ = BitVec.ofNat 64 i+BitVec.ofNat 64 8 := congrArg (fun w : Reg64 => w+BitVec.ofNat 64 8)
        ((congrFun ug 0).trans inv.index)
      _ = _ := bv_add i 8
  have tc : t.g 1 = BitVec.ofNat 64 (c.n-(i+8)) := by
    calc
      t.g 1 = u.g 1+BitVec.ofNat 64 18446744073709551608 := teC
      _ = BitVec.ofNat 64 (c.n-i)+BitVec.ofNat 64 18446744073709551608 := congrArg (fun w : Reg64 => w+BitVec.ofNat 64 18446744073709551608)
        ((congrFun ug 1).trans hcount)
      _ = BitVec.ofNat 64 ((c.n-i)-8) := minus8Bits _ (by have := valid.n64; omega) (by omega)
      _ = _ := congrArg (BitVec.ofNat 64) (by omega)
  have tp : Prefix initial.memory t.memory c.src c.dst c.n (i+8) := by
    rw [show t.memory = _ from teM,um]
    apply prefix_vector _ _ _ _ _ _ _ valid.buffers hi inv.progress
    intro j
    have haddr : c.src+4*i+4*j.val = c.src+4*(i+j.val) := by omega
    have hv := uv j
    simp only [readVec,haddr,inv.progress.unread (i+j.val) (by omega) (by have := j.isLt; omega)] at hv
    exact hv
  have ts : Safe c t.trace := by
    rw [show t.trace = _ from teT,ut]
    apply safe_append (safe_append inv.safe (safe_read (chunk_readable _ _ _ _ _ i 8 0 32 hi (by decide))))
    exact safe_write (chunk_writable _ _ i 8 0 32 hi (by decide))
  refine ⟨t,ur.trans tr,⟨tm.2.1.mpr ul,inv.fixed.trans (uf.trans tm.1),ti,tp,ts⟩,
    tm.2.2 uc,tc,?_⟩
  rw [show t.pc = _ from teP,ug,hcount,minus8Bits _ (by have := valid.n64; omega) (by omega)]
  rw [bv_ult 7 _ (by decide) (by have := valid.n64; omega)]
  have he : 7 < c.n-i-8 ↔ i+16 ≤ c.n := by omega
  simp only [decide_eq_true_eq,he]

end Div3Machine
