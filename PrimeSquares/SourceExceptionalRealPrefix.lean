import PrimeSquares.SourceHighRealPrefix
import PrimeSquares.FiniteExceptionalHigh
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceExceptional_real_prefix (M N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R)
    (q₀ : ℕ) (Q B : ℝ) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => r.den ≤ M)) N hN q₀ Q B χ κ β=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleExceptionalHigh N hN q₀ Q B χ κ β)) := by
  exact sourceCircle_symbol_prefix M hR _
end PrimeSquares
