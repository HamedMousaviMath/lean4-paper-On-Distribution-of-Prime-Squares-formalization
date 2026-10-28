import PrimeSquares.DyadicCircleErrorBudget
import PrimeSquares.CountableOperatorMaximum

open scoped lp
namespace PrimeSquares

noncomputable def dyadicCircleModelOperator (Q : ℝ)
    (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ) (j : ℕ) :
    ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  circleMajorArcOperator (sourceRationalCenters (sourceMajorArcScale (((2 : ℕ)^j : ℕ) : ℝ) Q))
    (2^j) (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))) (χ j) (κ j) (β j)

theorem dyadicCircleError_difference (Q : ℝ)
    (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ) (j : ℕ) :
    dyadicCircleErrorOperator Q χ κ β j =
      annularWeightedSquareAverage (P := 2) (by norm_num) (2^j) ArithmeticFunction.vonMangoldt -
        dyadicCircleModelOperator Q χ κ β j := by
  have h := circleModel_operator_decomposition
    (sourceRationalCenters (sourceMajorArcScale (((2 : ℕ)^j : ℕ) : ℝ) Q)) (2^j)
    (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))) (χ j) (κ j) (β j)
  apply eq_sub_iff_add_eq.mpr
  change circleMajorArcErrorOperator _ _ _ _ _ _+circleMajorArcOperator _ _ _ _ _ _ = _
  rw [add_comm]
  exact h.symm

theorem dyadicCircleError_difference_apply (Q : ℝ)
    (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ)
    (j : ℕ) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    dyadicCircleErrorOperator Q χ κ β j f x =
      annularWeightedSquareAverage (P := 2) (by norm_num) (2^j) ArithmeticFunction.vonMangoldt f x -
        dyadicCircleModelOperator Q χ κ β j f x := by
  rw [dyadicCircleError_difference]
  rfl

theorem dyadicCircleError_maximal_difference (Q : ℝ)
    (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ)
    (J : ℕ) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalValue (fun j => dyadicCircleErrorOperator Q χ κ β (J+j)) f x =
      ⨆ j : ℕ, ‖annularWeightedSquareAverage (P := 2) (by norm_num)
        (2^(J+j)) ArithmeticFunction.vonMangoldt f x - dyadicCircleModelOperator Q χ κ β (J+j) f x‖ := by
  unfold operatorMaximalValue
  congr 1
  funext j
  rw [dyadicCircleError_difference_apply]

end PrimeSquares
