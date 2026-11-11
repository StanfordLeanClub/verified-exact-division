/-
Exact division by an invariant floating-point divisor — the IEEE model is inhabited.

Every rational has a nearest float in a format with a minimal exponent (`exists_nearestB`), hence
a rounding function satisfying `RoundSpec` exists (`exists_round`).  The hypothesis on `R` in
`kernel_eq_div` is therefore satisfiable for every precision and exponent range.
-/
import ExactFDiv.Final

namespace ExactFDiv

/-- every float of the bounded format is an integer multiple of `2^emin` -/
theorem IsFloatB.exists_int {p : ℕ} {emin : ℤ} {f : ℚ} (h : IsFloatB p emin f) :
    ∃ k : ℤ, f = k * (2:ℚ) ^ emin := by
  obtain ⟨m, e, -, he, rfl⟩ := h
  refine ⟨m * 2 ^ (e - emin).toNat, ?_⟩
  have h4 : (2:ℚ) ^ e = 2 ^ (((e - emin).toNat : ℕ) : ℤ) * 2 ^ emin := by
    rw [← zpow_split]; congr 1; rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [h4]; push_cast; rw [zpow_natCast]; ring

theorem isFloatB_zero (p : ℕ) (emin : ℤ) : IsFloatB p emin 0 :=
  ⟨0, emin, by rw [abs_zero]; positivity, le_refl _, by simp⟩

/-- Existence of a nearest float (the candidates within `2|t|` form a finite set containing 0). -/
theorem exists_nearestB (p : ℕ) (emin : ℤ) (t : ℚ) : ∃ f, IsNearestB p emin t f := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 ^ emin := ⟨_, rfl⟩
  have hwpos : 0 < w := by rw [hw]; exact two_zpow_pos _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * |t| / w ≤ (N:ℚ) := exists_nat_ge _
  have hN' : 2 * |t| ≤ N * w := by
    rw [div_le_iff₀ hwpos] at hN; exact hN
  let S : Finset ℤ := (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun k => IsFloatB p emin ((k:ℚ) * w))
  have h0 : (0:ℤ) ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa using isFloatB_zero p emin
  obtain ⟨k0, hk0, hmin⟩ := S.exists_min_image (fun k : ℤ => |t - (k:ℚ) * w|) ⟨0, h0⟩
  refine ⟨(k0:ℚ) * w, (Finset.mem_filter.mp hk0).2, fun g hg => ?_⟩
  obtain ⟨k, hk⟩ := hg.exists_int
  rw [← hw] at hk
  rw [hk]
  by_cases hkS : k ∈ S
  · exact hmin k hkS
  · -- |k| > N, so |g| > 2|t| and g is farther from t than 0 is
    have hk0' := hmin 0 h0
    simp only [Int.cast_zero, zero_mul, sub_zero] at hk0'
    have hnot : ¬ (k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ)) := fun h =>
      hkS (Finset.mem_filter.mpr ⟨h, by rw [← hk]; exact hg⟩)
    rw [Finset.mem_Icc, not_and_or] at hnot
    have hbig : (N:ℚ) * w < |(k:ℚ) * w| := by
      rw [abs_mul, abs_of_pos hwpos]
      have h1 : (N:ℚ) < |(k:ℚ)| := by
        rcases hnot with h | h
        · push Not at h
          have h2 : (k:ℚ) < -(N:ℚ) := by exact_mod_cast h
          have h3 := neg_le_abs (k:ℚ)
          linarith
        · push Not at h
          have h2 : (N:ℚ) < (k:ℚ) := by exact_mod_cast h
          have h3 := le_abs_self (k:ℚ)
          linarith
      exact mul_lt_mul_of_pos_right h1 hwpos
    have h4 : |(k:ℚ) * w| ≤ |t| + |t - (k:ℚ) * w| := by
      have h5 := abs_sub t (t - (k:ℚ) * w)
      rwa [sub_sub_cancel] at h5
    linarith

/-- A rounding function satisfying `RoundSpec` exists. -/
theorem exists_round (p : ℕ) (emin emax : ℤ) :
    ∃ R : ℚ → IEEE, ∀ t, t ≠ 0 → RoundSpec p emin emax t (R t) := by
  classical
  have hex : ∀ t : ℚ, ∃ r, RoundSpec p emin emax t r := by
    intro t
    obtain ⟨f, hf⟩ := exists_nearestB p emin t
    by_cases h0 : f = 0
    · exact ⟨IEEE.zero (sgn t), f, hf, Or.inl ⟨h0, rfl⟩⟩
    · by_cases hm : |f| ≤ maxFloat p emax
      · exact ⟨IEEE.num f, f, hf, Or.inr (Or.inl ⟨h0, hm, rfl⟩)⟩
      · exact ⟨IEEE.inf (sgn f), f, hf, Or.inr (Or.inr ⟨not_le.mp hm, rfl⟩)⟩
  choose R hRspec using hex
  exact ⟨R, fun t _ => hRspec t⟩

end ExactFDiv
