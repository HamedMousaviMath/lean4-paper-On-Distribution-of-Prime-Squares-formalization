import PrimeSquares.FiniteExceptionalHigh
open Finset
namespace PrimeSquares
theorem circleExceptionalHighModel_collar (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (hΓ : ∀ r ∈ Γ,(r.den : ℝ) ≤ Q*(q₀ : ℝ)/B) :
    circleExceptionalHighModel Γ N hN q₀ Q B χ κ β=
      rationalCollarBlock Γ N hN (Q*(q₀ : ℝ)/B) (fun _ => β) (fun r => κ r*rationalTwistedGauss r (χ r)) := by
  unfold circleExceptionalHighModel rationalCollarBlock
  exact sum_congr rfl (fun r hr => circleExceptionalHigh_collar N hN hq₀ hQ hB χ κ β r (hΓ r hr))
end PrimeSquares
