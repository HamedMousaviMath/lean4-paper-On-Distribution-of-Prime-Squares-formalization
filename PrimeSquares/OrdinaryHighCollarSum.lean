import PrimeSquares.OrdinaryCircleHighCollar

open Finset
namespace PrimeSquares

theorem circleHighModel_ordinary_collar (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ Q) :
    circleHighModel Γ N hN q₀ Q B χ (fun _ => 0) β=
      rationalCollarBlock Γ N hN Q (fun _ => 1) rationalPrincipalGauss := by
  classical
  apply sum_congr rfl
  intro r hr
  exact circleHighTerm_ordinary_collar N hN q₀ hq₀ hQ hB χ β r (hden r hr)

end PrimeSquares
