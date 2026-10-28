import PrimeSquares.FiniteCircleModel
import PrimeSquares.FourierKernelSums

open Finset
namespace PrimeSquares

noncomputable def circleModelKernel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : ℤ → ℂ :=
  fourierKernel (circleMajorArcModel Γ N hN χ κ β)

noncomputable def circleModelErrorKernel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : ℤ → ℂ :=
  fourierKernel (circleMajorArcError Γ N hN χ κ β)

theorem circleModelKernel_sum (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (x : ℤ) :
    circleModelKernel Γ N hN χ κ β x =
      ∑ r ∈ Γ, fourierKernel (circleRationalModelTerm N hN χ κ β r) x :=
  fourierKernel_sum Γ _ x

theorem annularKernel_circle_decomposition (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (x : ℤ) :
    annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt x =
      circleModelKernel Γ N hN χ κ β x + circleModelErrorKernel Γ N hN χ κ β x := by
  unfold circleModelKernel circleModelErrorKernel circleMajorArcError
  rw [fourierKernel_sub]
  have he : fourierKernel (annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt) x =
      annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt x :=
    finiteSquareSymbol_kernel _ _ _ x
  rw [he]
  ring

end PrimeSquares
