import PrimeSquares.FiniteMaximalEnvelopeBound

open scoped lp
namespace PrimeSquares

noncomputable def countableOperatorEnvelope
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ∑' j : ℕ, magnitudeL2 (T j f)

theorem operator_magnitude_summable (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Summable (fun j : ℕ => magnitudeL2 (T j f)) := by
  apply (hT.mul_right ‖f‖).of_norm_bounded
  intro j
  rw [magnitudeL2_norm]
  exact (T j).le_opNorm f

theorem operator_magnitude_norm_summable (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Summable (fun j : ℕ => ‖magnitudeL2 (T j f)‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _ (hT.mul_right ‖f‖)
  intro j
  rw [magnitudeL2_norm]
  exact (T j).le_opNorm f

theorem countableOperatorEnvelope_norm (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    ‖countableOperatorEnvelope T f‖ ≤ (∑' j : ℕ, ‖T j‖)*‖f‖ := by
  have hs := operator_magnitude_norm_summable T hT f
  calc
    _ ≤ ∑' j : ℕ, ‖magnitudeL2 (T j f)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, ‖T j‖*‖f‖ := hs.tsum_le_tsum (fun j => by
      rw [magnitudeL2_norm]
      exact (T j).le_opNorm f) (hT.mul_right ‖f‖)
    _ = _ := tsum_mul_right

end PrimeSquares
