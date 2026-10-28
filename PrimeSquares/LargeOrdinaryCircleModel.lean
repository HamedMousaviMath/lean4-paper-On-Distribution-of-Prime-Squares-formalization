import PrimeSquares.LargeOrdinaryCircleTerm

open Finset
namespace PrimeSquares

theorem circleHighModel_large_ordinary (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (hden : ∀ r ∈ Γ,Q < (r.den : ℝ)) :
    circleHighModel Γ N hN q₀ Q B χ (fun _ => 0) β=circleMajorArcModel Γ N hN χ (fun _ => 0) β := by
  apply sum_congr rfl
  intro r hr
  exact circleHighTerm_large_ordinary N hN q₀ Q B χ β r (hden r hr)

end PrimeSquares
