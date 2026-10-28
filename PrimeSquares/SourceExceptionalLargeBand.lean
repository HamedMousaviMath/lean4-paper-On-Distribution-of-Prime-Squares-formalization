import PrimeSquares.SourceOrdinaryLargeBand
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceExceptional_large_band (M N : ℕ) (hN : 1 ≤ N) {W R : ℝ}
    (hW : 0 ≤ W) (hR : 0 ≤ R) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleExceptionalHighModel (((sourceRationalCenters R).filter (fun r => r.den ≤ M)).filter
      (fun r => W < (r.den : ℝ))) N hN q₀ Q B χ κ β=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleExceptionalHigh N hN q₀ Q B χ κ β))-
      realTruncatedCircleSymbol (M+1) (min W R) (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleExceptionalHigh N hN q₀ Q B χ κ β)) := by
  rw [source_denominator_block_universe hR M,filter_filter]
  exact rationalCircle_real_band _ M
    (fun r hr => ((mem_canonicalRationalCenters M r).mp hr).2) hW hR _
end PrimeSquares
