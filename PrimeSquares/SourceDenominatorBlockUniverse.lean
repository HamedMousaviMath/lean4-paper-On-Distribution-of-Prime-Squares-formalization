import PrimeSquares.CircleMajorArcPrefixIdentity
open Finset
namespace PrimeSquares
theorem source_denominator_block_universe {R : ℝ} (hR : 0 ≤ R) (M : ℕ) :
    (sourceRationalCenters R).filter (fun r => r.den ≤ M)=
      (canonicalRationalCenters M).filter (fun r => (r.den : ℝ) ≤ R) := by
  ext r
  simp only [mem_filter,mem_sourceRationalCenters hR,mem_canonicalRationalCenters]
  tauto
end PrimeSquares
