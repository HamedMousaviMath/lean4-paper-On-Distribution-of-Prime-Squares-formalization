import PrimeSquares.PrefixDifferenceMajorant
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceOrdinary_large_band (M N : ℕ) (hN : 1 ≤ N) {Q R : ℝ}
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleMajorArcModel (((sourceRationalCenters R).filter (fun r => r.den ≤ M)).filter
      (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleRationalModelTerm N hN χ (fun _ => 0) β))-
      realTruncatedCircleSymbol (M+1) (min Q R) (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleRationalModelTerm N hN χ (fun _ => 0) β)) := by
  rw [source_denominator_block_universe hR M,filter_filter]
  exact rationalCircle_real_band _ M
    (fun r hr => ((mem_canonicalRationalCenters M r).mp hr).2) hQ hR _
end PrimeSquares
