import Selector.Scaling

namespace CoefficientSelector
open ExactFDiv
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def div3Coeff : Coeff := ⟨(5592405 : ℚ) / 70368744177664, (11184811 : ℚ) / 2361183241434822606848, -47⟩
def div3Grid1 : GridCert := ⟨4194304, 4, 3, 1, -1⟩
def div3Grid2 : GridCert := ⟨4194304, 8, 3, 2, -5⟩
theorem div3_checked : check 24 12582912 div3Grid1 div3Grid2 div3Coeff = true := by decide +kernel
theorem div3_correct (X : ℤ) (hlo : (2:ℤ)^24 ≤ 2*X) (hhi : X < (2:ℤ)^24) :
    kernel 24 div3Coeff.h div3Coeff.l X = rneU 24 ((X:ℚ)/12582912) :=
  check_sound div3_checked hlo hhi

def repair32aCoeff : Coeff := ⟨(4574557 : ℚ) / 70368744177664, (1941357 : ℚ) / 590295810358705651712, -48⟩
def repair32aGrid1 : GridCert := ⟨1, 16777216, 15382635, 10322941, -11258813⟩
def repair32aGrid2 : GridCert := ⟨1, 33554432, 15382635, 12852788, -28036029⟩
theorem repair32a_checked : check 24 15382635 repair32aGrid1 repair32aGrid2 repair32aCoeff = true := by decide +kernel
theorem repair32a_correct (X : ℤ) (hlo : (2:ℤ)^24 ≤ 2*X) (hhi : X < (2:ℤ)^24) :
    kernel 24 repair32aCoeff.h repair32aCoeff.l X = rneU 24 ((X:ℚ)/15382635) :=
  check_sound repair32a_checked hlo hhi

def repair32aOriginal : Coeff := ⟨(4574557 : ℚ) / 70368744177664, (15530855 : ℚ) / 4722366482869645213696, -48⟩
theorem repair32a_original_rejected : check 24 15382635 repair32aGrid1 repair32aGrid2 repair32aOriginal = false := by decide +kernel
theorem repair32a_original_fails : kernel 24 repair32aOriginal.h repair32aOriginal.l 12852788 ≠
    rneU 24 ((12852788:ℚ)/15382635) := by decide +kernel
theorem repair32a_selected : select 24 15382635 repair32aGrid1 repair32aGrid2 [repair32aOriginal, repair32aCoeff] = some repair32aCoeff := by
  simp [select, repair32a_original_rejected, repair32a_checked]

def repair32bCoeff : Coeff := ⟨(9011031 : ℚ) / 140737488355328, (7821587 : ℚ) / 2361183241434822606848, -48⟩
def repair32bGrid1 : GridCert := ⟨1, 16777216, 15618355, 11343426, -12185093⟩
def repair32bGrid2 : GridCert := ⟨1, 33554432, 15618355, 5671713, -12185093⟩
theorem repair32b_checked : check 24 15618355 repair32bGrid1 repair32bGrid2 repair32bCoeff = true := by decide +kernel
theorem repair32b_correct (X : ℤ) (hlo : (2:ℤ)^24 ≤ 2*X) (hhi : X < (2:ℤ)^24) :
    kernel 24 repair32bCoeff.h repair32bCoeff.l X = rneU 24 ((X:ℚ)/15618355) :=
  check_sound repair32b_checked hlo hhi

def repair32bOriginal : Coeff := ⟨(9011031 : ℚ) / 140737488355328, (15643175 : ℚ) / 4722366482869645213696, -48⟩
theorem repair32b_original_rejected : check 24 15618355 repair32bGrid1 repair32bGrid2 repair32bOriginal = false := by decide +kernel
theorem repair32b_original_fails : kernel 24 repair32bOriginal.h repair32bOriginal.l 9946642 ≠
    rneU 24 ((9946642:ℚ)/15618355) := by decide +kernel
theorem repair32b_selected : select 24 15618355 repair32bGrid1 repair32bGrid2 [repair32bOriginal, repair32bCoeff] = some repair32bCoeff := by
  simp [select, repair32b_original_rejected, repair32b_checked]

def repair64Coeff : Coeff := ⟨(300553964844435 : ℚ) / 2535301200456458802993406410752, (8442363309020275 : ℚ) / 730750818665451459101842416358141509827966271488, -106⟩
def repair64Grid1 : GridCert := ⟨1, 9007199254740992, 8435427567121651, 3187505974177413, -3403562084629445⟩
def repair64Grid2 : GridCert := ⟨1, 18014398509481984, 8435427567121651, 5811466770649532, -12410761339370437⟩
theorem repair64_checked : check 53 8435427567121651 repair64Grid1 repair64Grid2 repair64Coeff = true := by decide +kernel
theorem repair64_correct (X : ℤ) (hlo : (2:ℤ)^53 ≤ 2*X) (hhi : X < (2:ℤ)^53) :
    kernel 53 repair64Coeff.h repair64Coeff.l X = rneU 53 ((X:ℚ)/8435427567121651) :=
  check_sound repair64_checked hlo hhi

def repair64Original : Coeff := ⟨(300553964844435 : ℚ) / 2535301200456458802993406410752, (4221181654510137 : ℚ) / 365375409332725729550921208179070754913983135744, -106⟩
theorem repair64_original_rejected : check 53 8435427567121651 repair64Grid1 repair64Grid2 repair64Original = false := by decide +kernel
theorem repair64_original_fails : kernel 53 repair64Original.h repair64Original.l 5811466770649532 ≠
    rneU 53 ((5811466770649532:ℚ)/8435427567121651) := by decide +kernel
theorem repair64_selected : select 53 8435427567121651 repair64Grid1 repair64Grid2 [repair64Original, repair64Coeff] = some repair64Coeff := by
  simp [select, repair64_original_rejected, repair64_checked]

theorem malformed_grid_rejected : check 24 12582912 ⟨1, 1, 1, 1, 1⟩ div3Grid2 div3Coeff = false := by decide +kernel
theorem div3_selected : select 24 12582912 div3Grid1 div3Grid2 [div3Coeff] = some div3Coeff := by
  simp [select, div3_checked]

theorem div3_scaled_correct (X i : ℤ) (hlo : (2:ℤ)^24 ≤ 2*X) (hhi : X < (2:ℤ)^24)
    {s : ℚ} (hs : s = 1 ∨ s = -1) :
    kernel 24 ((5592405:ℚ)/16777216) ((11184811:ℚ)/562949953421312) (s*X*2^i) =
      rneU 24 ((s*X*2^i)/3) := by
  have h := check_sound_scaled div3_checked hlo hhi hs i (-22)
  norm_num [div3Coeff] at h
  exact h

end CoefficientSelector
