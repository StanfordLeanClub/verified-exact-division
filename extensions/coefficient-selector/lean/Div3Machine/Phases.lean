import Div3Machine.Loops

namespace Div3Machine
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

theorem initial_phase (fp : IEEEInstructions) (c : Config) (initial : State)
    (valid : Valid c) (arg : Args c initial) (hl : Loaded initial.memory c.image)
    (hp : initial.pc=0) (ha : alive initial) (ht : initial.trace=[]) :
    ∃ t i, Reaches fp program initial t ∧ Inv c initial t i ∧
      i ≤ c.n ∧ c.n < i+32 ∧ t.pc=0x11a := by
  let s := evalBlock fp b_enter initial
  have sr := reaches_at fp b_enter initial b_enter_ok hp ha
  have sm := block_control_meta fp b_enter initial (by decide +kernel)
  rcases enter_effect fp initial with ⟨ss,sg,sv,st,sp⟩
  have sa : Args c s := arg.of_fixed sm.1
  have sl : alive s := sm.2.mpr ha
  have sp' : s.pc = if c.n < 32 then 0x118 else 0xa := by
    rw [show s.pc = _ from sp,arg.n,bv_ult c.n 32 valid.n64 (by decide)]
    simp only [decide_eq_true_eq]
  by_cases hn : c.n < 32
  · have pp : s.pc=0x118 := by simpa only [if_pos hn] using sp'
    let u := evalBlock fp b_skip32 s
    have ur := reaches_at fp b_skip32 s b_skip32_ok pp sl
    have bm := block_control_meta fp b_skip32 s (by decide +kernel)
    rcases skip32_effect fp s with ⟨mm,ii,pp',tt⟩
    have inv : Inv c initial u 0 := by
      refine ⟨bm.2.mpr sl,sm.1.trans bm.1,ii,?_,?_⟩
      · rw [show u.memory = _ from mm,ss]
        exact prefix_zero _ _ _ _
      · rw [show u.trace = _ from tt,st,ht]
        intro x hx; simp at hx
    exact ⟨u,0,sr.trans ur,inv,by omega,by omega,pp'⟩
  · have pp : s.pc=0xa := by simpa only [if_neg hn] using sp'
    have sc : ImageConstants s := by
      apply loaded_constants
      · rw [show s.memory=initial.memory from ss,sa.image]; exact hl
      · rw [sa.image]; exact valid.imageBound
    let u := evalBlock fp b_setup32 s
    have ur := reaches_at fp b_setup32 s b_setup32_ok pp sl
    have bm := block_control_meta fp b_setup32 s (by decide +kernel)
    rcases setup32_effect fp s sc with ⟨mm,ii,cc,uc,up,tt⟩
    have inv : Inv c initial u 0 := by
      refine ⟨bm.2.mpr sl,sm.1.trans bm.1,ii,?_,?_⟩
      · rw [show u.memory = _ from mm,ss]; exact prefix_zero _ _ _ _
      · rw [show u.trace = _ from tt,st,ht,List.nil_append]
        exact safe_constants sa valid
    have count : u.g 1 = BitVec.ofNat 64 (c.n/32) := by
      rw [show u.g 1 = _ from cc,sa.n,setup_count c.n valid.n64 (by omega)]
    have np : 0 < c.n/32 := by omega
    have pc : u.pc = if c.n/32=0 then 0x104 else 0x50 := by
      simpa only [if_neg (by omega : c.n/32 ≠ 0)] using up
    obtain ⟨t,i,tr,ti,tn,tend,tp⟩ := loop32 fp c initial u 0 (c.n/32) valid arg inv uc
      (by omega) (by omega) pc count
    exact ⟨t,i,sr.trans (ur.trans tr),ti,tn,tend,tp⟩

theorem vector_phase (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (hl : Loaded initial.memory c.image)
    (inv : Inv c initial s i) (hi : i ≤ c.n) (hp : s.pc=0x11a) :
    ∃ t j, Reaches fp program s t ∧ Inv c initial t j ∧
      j ≤ c.n ∧ c.n < j+8 ∧ t.pc=0x19c := by
  let u := evalBlock fp b_check8 s
  have ur := reaches_at fp b_check8 s b_check8_ok hp inv.live
  have bm := block_control_meta fp b_check8 s (by decide +kernel)
  rcases check8_effect fp s with ⟨mm,ii,cc,pp,tt⟩
  have ui : Inv c initial u i := inv.unchanged bm.1 (bm.2.mpr inv.live) ii mm (by rw [tt]; exact inv.safe)
  have sa := arg.of_fixed inv.fixed
  have cc' : u.g 1 = BitVec.ofNat 64 (c.n-i) := by
    rw [show u.g 1 = _ from cc,sa.n,inv.index,bv_sub c.n i hi valid.n64]
  have pp' : u.pc = if c.n-i < 8 then 0x19c else 0x126 := by
    rw [show u.pc = _ from pp,sa.n,inv.index,bv_sub c.n i hi valid.n64,
      bv_ult _ 8 (by have := valid.n64; omega) (by decide)]
    simp only [decide_eq_true_eq]
  by_cases h8 : c.n-i < 8
  · exact ⟨u,i,ur,ui,hi,by omega,by simpa only [if_pos h8] using pp'⟩
  · have uc := ui.image_constants arg valid hi hl
    have up : u.pc=0x126 := by simpa only [if_neg h8] using pp'
    let v := evalBlock fp b_setup8 u
    have vr := reaches_at fp b_setup8 u b_setup8_ok up ui.live
    have vm := block_control_meta fp b_setup8 u (by decide +kernel)
    rcases setup8_effect fp u uc with ⟨vmm,vgg,vc,vp,vt⟩
    have vi : Inv c initial v i := ui.unchanged vm.1 (vm.2.mpr ui.live) (congrFun vgg 0) vmm (by
      rw [vt]; exact safe_append ui.safe (safe_constants (arg.of_fixed ui.fixed) valid))
    have vcount : v.g 1 = BitVec.ofNat 64 (c.n-i) := (congrFun vgg 1).trans cc'
    have vpc : v.pc = if i+8 ≤ c.n then 0x160 else 0x194 := by
      simpa only [if_pos (by omega : i+8 ≤ c.n)] using vp
    obtain ⟨t,j,tr,ti,tj,tend,tp⟩ := loop8 fp c initial v i valid arg vi vc hi vpc vcount
    exact ⟨t,j,ur.trans (vr.trans tr),ti,tj,tend,tp⟩

theorem scalar_phase (fp : IEEEInstructions) (c : Config) (initial s : State) (i : ℕ)
    (valid : Valid c) (arg : Args c initial) (hl : Loaded initial.memory c.image)
    (inv : Inv c initial s i) (hi : i ≤ c.n) (hp : s.pc=0x19c) :
    ∃ t, Reaches fp program s t ∧ Inv c initial t c.n ∧ t.pc=0x1f5 := by
  let u := evalBlock fp b_check1 s
  have ur := reaches_at fp b_check1 s b_check1_ok hp inv.live
  have bm := block_control_meta fp b_check1 s (by decide +kernel)
  rcases check1_effect fp s with ⟨mm,gg,pp,tt⟩
  have ui : Inv c initial u i := inv.unchanged bm.1 (bm.2.mpr inv.live) (congrFun gg 0) mm (by rw [tt]; exact inv.safe)
  have sa := arg.of_fixed inv.fixed
  have pp' : u.pc = if i < c.n then 0x1a1 else 0x1f5 := by
    rw [show u.pc = _ from pp,inv.index,sa.n,bv_ult i c.n (by have := valid.n64; omega) valid.n64]
    simp only [decide_eq_true_eq]
  by_cases h1 : i<c.n
  · have up : u.pc=0x1a1 := by simpa only [if_pos h1] using pp'
    have uc := ui.image_constants arg valid hi hl
    let v := evalBlock fp b_setup1 u
    have vr := reaches_at fp b_setup1 u b_setup1_ok up ui.live
    have vm := block_control_meta fp b_setup1 u (by decide +kernel)
    rcases setup1_effect fp u uc with ⟨vmm,vgg,vc,vp,vt⟩
    have vs : Safe c v.trace := by
      rw [vt]
      apply safe_append ui.safe
      have hs := safe_constants (arg.of_fixed ui.fixed) valid
      intro x hx
      apply hs x
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [constantReads]
    have vi : Inv c initial v i := ui.unchanged vm.1 (vm.2.mpr ui.live) (congrFun vgg 0) vmm vs
    have vpc : v.pc=if i=c.n then 0x1f5 else 0x1cd := by
      simpa only [if_neg (by omega : i ≠ c.n)] using vp
    obtain ⟨t,tr,ti,tp⟩ := loop1 fp c initial v i valid arg vi vc hi vpc
    exact ⟨t,ur.trans (vr.trans tr),ti,tp⟩
  · have he : i=c.n := by omega
    subst i
    exact ⟨u,ur,ui,by simpa only [if_neg h1] using pp'⟩

end Div3Machine
