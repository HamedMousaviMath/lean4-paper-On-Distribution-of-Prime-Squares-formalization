import PrimeSquares.UniformSourceLowDyadicMaximum

open Finset
namespace PrimeSquares

theorem circleHighModel_denominator_split (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B : ℝ) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleHighModel Γ N hN q₀ Q B χ κ β=
      circleHighModel (Γ.filter (fun r => (r.den : ℝ) ≤ Q)) N hN q₀ Q B χ κ β+
      circleHighModel (Γ.filter (fun r => Q < (r.den : ℝ))) N hN q₀ Q B χ κ β := by
  classical
  symm
  simpa only [circleHighModel, not_le] using sum_filter_add_sum_filter_not Γ
    (fun r : ℚ => (r.den : ℝ) ≤ Q) (fun r => circleHighTerm N hN q₀ Q B χ κ β r)

end PrimeSquares
