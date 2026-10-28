import PrimeSquares.RationalCircleRealPrefix
import PrimeSquares.SourceDenominatorBlockUniverse
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceCircle_symbol_prefix (M : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (F : ℚ → C(PrimeCircle,ℂ)) :
    (∑ r ∈ (sourceRationalCenters R).filter (fun r => r.den ≤ M),F r)=
      realTruncatedCircleSymbol (M+1) R
        (rationalCircleDenominatorBlock (canonicalRationalCenters M) F) := by
  rw [source_denominator_block_universe hR M]
  exact rationalCircle_real_prefix _ M
    (fun r hr => ((mem_canonicalRationalCenters M r).mp hr).2) hR F
end PrimeSquares
