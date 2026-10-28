import PrimeSquares.ConductorOutsideSource

namespace PrimeSquares

theorem sourceFullLow_squared {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2) :
    circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β=
      realCombinedLowModel N hN q₀ χ₀ Q (by linarith) (source_squared_low_width hQ hQR hb) β ⌊R⌋₊ active := by
  by_cases hqR : (q₀ : ℝ) ≤ R
  · exact sourceFullLow_squared_level hN q₀ χ₀ active β hQ hQR hqR hb
  · have hR : 1 ≤ R := hQ.trans hQR
    have hq : R < (q₀ : ℝ) := lt_of_not_ge hqR
    have hweak : 2*R^4 ≤ (N : ℝ)^2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by norm_num : 4 ≤ 8)) (by norm_num : (0 : ℝ) ≤ 2)).trans hb
    have hM : ⌊R⌋₊ < q₀ := by exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ R)).trans_lt hq
    rw [sourceLowModel_conductor_outside N hN q₀ χ₀ Q R β active (by linarith) hq,
      sourceLowModel_no_exception hN hQ hQR hweak q₀ (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀) β]
    unfold realCombinedLowModel
    rw [realExceptionalLowModel_empty _ _ _ _ _ _ _ _ hM]
    simp only [ite_self,sub_zero]

end PrimeSquares
