import PrimeSquares.SquareFunctionMembership

open scoped lp
namespace PrimeSquares

theorem squareFunctionL2_norm_square (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    ‖squareFunctionL2 F hF‖^2=∑' j : ℕ,‖F j‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (squareFunctionL2 F hF)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,squareFunctionL2,Real.norm_eq_abs,sq_abs,
    squareFunctionValue_sq,coordinate_square_total F hF] using h

theorem squareFunctionL2_norm (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    ‖squareFunctionL2 F hF‖=Real.sqrt (∑' j : ℕ,‖F j‖^2) := by
  rw [←squareFunctionL2_norm_square F hF,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

end PrimeSquares
