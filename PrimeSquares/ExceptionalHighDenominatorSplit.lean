import PrimeSquares.SourceExceptionalCollarMaximum
open Finset
namespace PrimeSquares
theorem circleExceptionalHighModel_denominator_split (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B W : ℝ) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleExceptionalHighModel Γ N hN q₀ Q B χ κ β=
      circleExceptionalHighModel (Γ.filter (fun r => (r.den : ℝ) ≤ W)) N hN q₀ Q B χ κ β+
      circleExceptionalHighModel (Γ.filter (fun r => W < (r.den : ℝ))) N hN q₀ Q B χ κ β := by
  classical
  symm
  simpa only [circleExceptionalHighModel,not_le] using sum_filter_add_sum_filter_not Γ
    (fun r : ℚ => (r.den : ℝ) ≤ W) (fun r => circleExceptionalHigh N hN q₀ Q B χ κ β r)
end PrimeSquares
