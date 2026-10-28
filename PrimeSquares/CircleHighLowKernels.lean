import PrimeSquares.FiniteCircleHighLow
import PrimeSquares.CircleModelKernels

namespace PrimeSquares

noncomputable def circleLowKernel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : ℤ → ℂ :=
  fourierKernel (circleLowModel Γ N hN q₀ Q B₀ χ κ β)

noncomputable def circleHighKernel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : ℤ → ℂ :=
  fourierKernel (circleHighModel Γ N hN q₀ Q B₀ χ κ β)

theorem circleKernel_low_add_high (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (x : ℤ) :
    circleLowKernel Γ N hN q₀ Q B₀ χ κ β x + circleHighKernel Γ N hN q₀ Q B₀ χ κ β x =
      circleModelKernel Γ N hN χ κ β x := by
  unfold circleLowKernel circleHighKernel circleModelKernel
  rw [←fourierKernel_add,circleModel_low_add_high]

theorem annularKernel_circle_low_high_error (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β : ℝ) (x : ℤ) :
    annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt x =
      circleLowKernel Γ N hN q₀ Q B₀ χ κ β x + circleHighKernel Γ N hN q₀ Q B₀ χ κ β x +
      circleModelErrorKernel Γ N hN χ κ β x := by
  rw [circleKernel_low_add_high]
  exact annularKernel_circle_decomposition Γ N hN χ κ β x

end PrimeSquares
