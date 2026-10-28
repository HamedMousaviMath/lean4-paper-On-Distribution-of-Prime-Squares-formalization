import PrimeSquares.OperatorSquareMaximal

open scoped lp
namespace PrimeSquares

theorem operator_output_square_summable (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f : ℓ²(ℤ, ℂ)) :
    Summable (fun j : ℕ => ‖T j f‖^2) := by
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ (hT.mul_right (‖f‖^2))
  intro j
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ((T j).le_opNorm f) 2

theorem operator_output_square_total (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f : ℓ²(ℤ, ℂ)) :
    (∑' j : ℕ,‖T j f‖^2) ≤ (∑' j : ℕ,‖T j‖^2)*‖f‖^2 := by
  rw [←tsum_mul_right]
  apply (operator_output_square_summable T hT f).tsum_le_tsum _ (hT.mul_right (‖f‖^2))
  intro j
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ((T j).le_opNorm f) 2

theorem operator_squares_countable_maximal (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f : ℓ²(ℤ, ℂ)) :
    ‖squareMaximumL2 (fun j => T j f) (operator_output_square_summable T hT f)‖ ≤
      Real.sqrt (∑' j : ℕ,‖T j‖^2)*‖f‖ := by
  apply (squareMaximumL2_norm _ _).trans
  calc
    _ ≤ Real.sqrt ((∑' j : ℕ,‖T j‖^2)*‖f‖^2) := Real.sqrt_le_sqrt (operator_output_square_total T hT f)
    _ = _ := by rw [Real.sqrt_mul (tsum_nonneg (fun j => sq_nonneg _)),Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

end PrimeSquares
