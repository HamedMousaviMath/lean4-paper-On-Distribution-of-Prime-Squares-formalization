import PrimeSquares.FiniteCircleModel
import PrimeSquares.CircleMultipliers

open scoped lp
namespace PrimeSquares

noncomputable def circleMajorArcOperator (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) := integerMultiplier (circleMajorArcModel Γ N hN χ κ β)

noncomputable def circleMajorArcErrorOperator (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) := integerMultiplier (circleMajorArcError Γ N hN χ κ β)

theorem circleModel_operator_decomposition (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt =
      circleMajorArcOperator Γ N hN χ κ β + circleMajorArcErrorOperator Γ N hN χ κ β := by
  rw [annularWeightedSquareAverage_l2_multiplier]
  simp only [circleMajorArcOperator, circleMajorArcErrorOperator, circleMajorArcError,
    integerMultiplier_sub, add_sub_cancel]

theorem circleModel_error_operator_bound (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    {B : ℝ} (hB : 0 ≤ B) (he : ∀ θ, ‖circleMajorArcError Γ N hN χ κ β θ‖ ≤ B) :
    ‖circleMajorArcErrorOperator Γ N hN χ κ β‖ ≤ B :=
  integerMultiplier_opNorm_le_of_bound _ hB he

end PrimeSquares
