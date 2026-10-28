import PrimeSquares.RationalRealPrefixGrouping
open Finset
namespace PrimeSquares
theorem circleMajorArcModel_real_prefix (Γ : Finset ℚ) (M : ℕ) (hΓ : ∀ r ∈ Γ,r.den ≤ M)
    {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleMajorArcModel (Γ.filter (fun r => (r.den : ℝ) ≤ R)) N hN χ κ β=
      ∑ q ∈ range (min (M+1) (⌊R⌋₊+1)),circleMajorArcModel (Γ.filter (fun r => r.den=q)) N hN χ κ β := by
  exact rational_real_prefix_grouping Γ M hΓ hR (fun r => circleRationalModelTerm N hN χ κ β r)
end PrimeSquares
