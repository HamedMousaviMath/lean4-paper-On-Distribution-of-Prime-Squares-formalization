import PrimeSquares.CircleHighLowOperators
import PrimeSquares.CircleModelConvolution

open Finset
namespace PrimeSquares

theorem annularKernel_finite_low_high_error (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β : ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x =
      circleLowOperator Γ N hN q₀ Q B₀ χ κ β (finiteInputLp F f 1) x +
      circleHighOperator Γ N hN q₀ Q B₀ χ κ β (finiteInputLp F f 2) x +
      circleMajorArcErrorOperator Γ N hN χ κ β (finiteInputLp F f 2) x := by
  rw [circleLowOperator_finite,circleHighOperator_finite,circleModelErrorOperator_finite_convolution]
  unfold finiteConvolution
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro y _
  rw [annularKernel_circle_low_high_error Γ N hN q₀ Q B₀ χ κ β]
  ring

end PrimeSquares
