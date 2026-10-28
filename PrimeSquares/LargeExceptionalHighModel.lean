import PrimeSquares.ExceptionalHighDenominatorSplit
open Finset
namespace PrimeSquares
theorem circleExceptionalHighModel_large (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (hΓ : ∀ r ∈ Γ,Q*(q₀ : ℝ)/B < (r.den : ℝ)) :
    circleExceptionalHighModel Γ N hN q₀ Q B χ κ β=
      circleMajorArcModel Γ N hN χ (fun _ => 0) β-circleMajorArcModel Γ N hN χ κ β := by
  unfold circleExceptionalHighModel circleMajorArcModel
  rw [←sum_sub_distrib]
  exact sum_congr rfl (fun r hr => circleExceptionalHigh_large N hN hq₀ hQ hB χ κ β r (hΓ r hr))
end PrimeSquares
