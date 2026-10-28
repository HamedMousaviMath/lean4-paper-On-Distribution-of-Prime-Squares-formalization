import PrimeSquares.SquareEnergyFubini

open scoped lp
namespace PrimeSquares

noncomputable def squareFunctionValue (F : ℕ → ℓ²(ℤ, ℂ)) (x : ℤ) : ℝ := Real.sqrt (∑' j : ℕ,‖F j x‖^2)

theorem squareFunctionValue_nonneg (F : ℕ → ℓ²(ℤ, ℂ)) (x : ℤ) : 0 ≤ squareFunctionValue F x := Real.sqrt_nonneg _

theorem squareFunctionValue_sq (F : ℕ → ℓ²(ℤ, ℂ)) (x : ℤ) :
    (squareFunctionValue F x)^2=∑' j : ℕ,‖F j x‖^2 := Real.sq_sqrt (tsum_nonneg (fun j => sq_nonneg ‖F j x‖))

theorem squareFunctionValue_dominates (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (j : ℕ) (x : ℤ) :
    ‖F j x‖ ≤ squareFunctionValue F x := by
  apply (Real.le_sqrt (norm_nonneg _) (tsum_nonneg (fun i => sq_nonneg ‖F i x‖))).mpr
  exact (coordinate_square_summable F hF x).le_tsum j (fun i _ => sq_nonneg _)

end PrimeSquares
