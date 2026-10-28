import PrimeSquares.SourceCircleSymbolPrefix
import PrimeSquares.FiniteCircleHighLow
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceHigh_real_prefix (M N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R)
    (q₀ : ℕ) (Q B : ℝ) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleHighModel ((sourceRationalCenters R).filter (fun r => r.den ≤ M)) N hN q₀ Q B χ κ β=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleHighTerm N hN q₀ Q B χ κ β)) := by
  exact sourceCircle_symbol_prefix M hR _
end PrimeSquares
