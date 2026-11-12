import Div3IEEE.Array
namespace Div3IEEE
open ExactFDiv
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem case_positive_zero : nativeGuarded (BitVec.ofNat 32 0) = decode (BitVec.ofNat 32 0) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_zero : nativeGuarded (BitVec.ofNat 32 2147483648) = decode (BitVec.ofNat 32 2147483648) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_min_subnormal : nativeGuarded (BitVec.ofNat 32 1) = decode (BitVec.ofNat 32 0) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_min_subnormal : nativeGuarded (BitVec.ofNat 32 2147483649) = decode (BitVec.ofNat 32 2147483648) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_two_subnormal_quanta : nativeGuarded (BitVec.ofNat 32 2) = decode (BitVec.ofNat 32 1) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_two_quanta : nativeGuarded (BitVec.ofNat 32 2147483650) = decode (BitVec.ofNat 32 2147483649) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_three_subnormal_quanta : nativeGuarded (BitVec.ofNat 32 3) = decode (BitVec.ofNat 32 1) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_max_subnormal : nativeGuarded (BitVec.ofNat 32 8388607) = decode (BitVec.ofNat 32 2796202) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_min_normal : nativeGuarded (BitVec.ofNat 32 8388608) = decode (BitVec.ofNat 32 2796203) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_min_normal : nativeGuarded (BitVec.ofNat 32 2155872256) = decode (BitVec.ofNat 32 2150279851) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_first_normal_quotient : nativeGuarded (BitVec.ofNat 32 20971520) = decode (BitVec.ofNat 32 8388608) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_below_guard : nativeGuarded (BitVec.ofNat 32 226492415) = decode (BitVec.ofNat 32 212511402) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_at_guard : nativeGuarded (BitVec.ofNat 32 226492416) = decode (BitVec.ofNat 32 212511403) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_above_guard : nativeGuarded (BitVec.ofNat 32 226492417) = decode (BitVec.ofNat 32 212511404) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_three : nativeGuarded (BitVec.ofNat 32 1077936128) = decode (BitVec.ofNat 32 1065353216) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_max_finite : nativeGuarded (BitVec.ofNat 32 2139095039) = decode (BitVec.ofNat 32 2125114026) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_max_finite : nativeGuarded (BitVec.ofNat 32 4286578687) = decode (BitVec.ofNat 32 4272597674) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_positive_infinity : nativeGuarded (BitVec.ofNat 32 2139095040) = decode (BitVec.ofNat 32 2139095040) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_infinity : nativeGuarded (BitVec.ofNat 32 4286578688) = decode (BitVec.ofNat 32 4286578688) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_quiet_nan : nativeGuarded (BitVec.ofNat 32 2143363909) = decode (BitVec.ofNat 32 2143289344) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_quiet_nan : nativeGuarded (BitVec.ofNat 32 4290847557) = decode (BitVec.ofNat 32 2143289344) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_signaling_nan : nativeGuarded (BitVec.ofNat 32 2139169605) = decode (BitVec.ofNat 32 2143289344) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem case_negative_signaling_nan : nativeGuarded (BitVec.ofNat 32 4286653253) = decode (BitVec.ofNat 32 2143289344) := by
  rw [nativeGuarded_correct]
  decide +kernel

theorem unguarded_min_normal_wrong :
    raw (decode (BitVec.ofNat 32 0x00800000)) = decode (BitVec.ofNat 32 0x002aaaaa) := by decide +kernel
theorem unguarded_fails :
    raw (decode (BitVec.ofNat 32 0x00800000)) ≠ reference (decode (BitVec.ofNat 32 0x00800000)) := by decide +kernel

/-- The low multiply at x=3 is inexact although the reference quotient is exact.
This is why equality of sticky exception flags is not a valid extension of the value claim. -/
theorem three_low_product_inexact : rne 24 (-149) (3*lo) ≠ 3*lo := by decide +kernel
theorem three_reference_exact : rne 24 (-149) ((3:ℚ)/3) = 1 := by decide +kernel

end Div3IEEE
