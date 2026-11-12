import Div3Machine.Body32
import Div3Machine.Body8
import Div3Machine.Body1

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

theorem loop8 (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : Constants s) (hi : i ≤ c.n)
    (hp : s.pc = (if i+8 ≤ c.n then 0x160 else 0x194))
    (hcount : s.g 1 = BitVec.ofNat 64 (c.n-i)) :
    ∃ t j, Reaches fp program s t ∧ Inv c initial t j ∧
      j ≤ c.n ∧ c.n < j+8 ∧ t.pc = 0x19c := by
  by_cases h8 : i+8 ≤ c.n
  · have pp : s.pc = 0x160 := by simpa only [if_pos h8] using hp
    obtain ⟨u,ur,ui,uc,un,up⟩ := step8 fp c initial s i valid arg inv hc h8 pp hcount
    have pp' : u.pc = (if (i+8)+8 ≤ c.n then 0x160 else 0x194) := by
      simpa only [show i+8+8=i+16 by omega] using up
    obtain ⟨t,j,tr,ti,tj,tend,tp⟩ := loop8 fp c initial u (i+8) valid arg ui uc h8 pp' un
    exact ⟨t,j,ur.trans tr,ti,tj,tend,tp⟩
  · have pp : s.pc = 0x194 := by simpa only [if_neg h8] using hp
    let t := evalBlock fp b_exit8 s
    have tr := reaches_at fp b_exit8 s b_exit8_ok pp inv.live
    have tm := block_meta fp b_exit8 s (by decide +kernel)
    have te := exit8_effect fp s
    have ti : Inv c initial t i := inv.unchanged tm.1 (tm.2.1.mpr inv.live) rfl rfl inv.safe
    exact ⟨t,i,tr,ti,hi,by omega,rfl⟩
termination_by c.n-i
decreasing_by omega

theorem loop1 (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : ScalarConstants s) (hi : i ≤ c.n)
    (hp : s.pc = (if i=c.n then 0x1f5 else 0x1cd)) :
    ∃ t, Reaches fp program s t ∧ Inv c initial t c.n ∧ t.pc = 0x1f5 := by
  by_cases he : i=c.n
  · subst i
    exact ⟨s,⟨0,rfl⟩,inv,by simpa only [if_true] using hp⟩
  · have pp : s.pc = 0x1cd := by simpa only [if_neg he] using hp
    obtain ⟨u,ur,ui,uc,up⟩ := step1 fp c initial s i valid arg inv hc (by omega) pp
    obtain ⟨t,tr,ti,tp⟩ := loop1 fp c initial u (i+1) valid arg ui uc (by omega) up
    exact ⟨t,ur.trans tr,ti,tp⟩
termination_by c.n-i
decreasing_by omega

theorem loop32 (fp : IEEEInstructions) (c : Config) (initial s : State) (i q : ℕ)
    (valid : Valid c) (arg : Args c initial) (inv : Inv c initial s i)
    (hc : Constants s) (hi : i+32*q ≤ c.n) (hr : c.n < i+32*(q+1))
    (hp : s.pc = (if q=0 then 0x104 else 0x50))
    (hcount : s.g 1 = BitVec.ofNat 64 q) :
    ∃ t j, Reaches fp program s t ∧ Inv c initial t j ∧
      j ≤ c.n ∧ c.n < j+32 ∧ t.pc = 0x11a := by
  cases q with
  | zero =>
    have pp : s.pc = 0x104 := by simpa only [if_true] using hp
    let t := evalBlock fp b_exit32 s
    have tr := reaches_at fp b_exit32 s b_exit32_ok pp inv.live
    have tm := block_meta fp b_exit32 s (by decide +kernel)
    have ti : Inv c initial t i := inv.unchanged tm.1 (tm.2.1.mpr inv.live) rfl rfl inv.safe
    exact ⟨t,i,tr,ti,by omega,by omega,rfl⟩
  | succ q =>
    have pp : s.pc = 0x50 := by simpa only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false] using hp
    obtain ⟨u,ur,ui,uc,un,up⟩ := step32 fp c initial s i q valid arg inv hc (by omega) pp
      (by have := valid.n64; omega) hcount
    obtain ⟨t,j,tr,ti,tj,tend,tp⟩ := loop32 fp c initial u (i+32) q valid arg ui uc (by omega) (by omega) up un
    exact ⟨t,j,ur.trans tr,ti,tj,tend,tp⟩
termination_by q

end Div3Machine
