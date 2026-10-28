import PrimeSquares.SourceDenominatorBlockUniverse
open Finset
namespace PrimeSquares
theorem source_circle_block_prefix {R : ℝ} (hR : 0 ≤ R) (M N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleMajorArcModel ((sourceRationalCenters R).filter (fun r => r.den ≤ M)) N hN χ κ β=
      ∑ q ∈ range (min (M+1) (⌊R⌋₊+1)),
        circleMajorArcModel ((canonicalRationalCenters M).filter (fun r => r.den=q)) N hN χ κ β := by
  rw [source_denominator_block_universe hR M]
  exact circleMajorArcModel_real_prefix _ M (fun r hr => ((mem_canonicalRationalCenters M r).mp hr).2) hR N hN χ κ β
end PrimeSquares
