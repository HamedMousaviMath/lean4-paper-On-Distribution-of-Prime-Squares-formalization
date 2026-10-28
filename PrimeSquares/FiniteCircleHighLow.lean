import PrimeSquares.CircleHighTerm
import PrimeSquares.FiniteCircleModel

open Finset
namespace PrimeSquares

noncomputable def circleLowModel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle, ℂ) :=
  ∑ r ∈ Γ, circleLowTerm N hN q₀ Q B₀ χ κ β r

noncomputable def circleHighModel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle, ℂ) :=
  ∑ r ∈ Γ, circleHighTerm N hN q₀ Q B₀ χ κ β r

theorem circleModel_low_add_high (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleLowModel Γ N hN q₀ Q B₀ χ κ β + circleHighModel Γ N hN q₀ Q B₀ χ κ β =
      circleMajorArcModel Γ N hN χ κ β := by
  simp only [circleLowModel,circleHighModel,circleMajorArcModel,←sum_add_distrib,
    circleTerm_low_add_high]

theorem annularSymbol_circle_low_high_error (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt =
      circleLowModel Γ N hN q₀ Q B₀ χ κ β + circleHighModel Γ N hN q₀ Q B₀ χ κ β +
      circleMajorArcError Γ N hN χ κ β := by
  rw [circleModel_low_add_high,circleMajorArcError]
  ring

end PrimeSquares
