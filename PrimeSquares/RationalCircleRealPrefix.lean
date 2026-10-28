import PrimeSquares.RationalCircleDenominatorBlocks
import PrimeSquares.RationalRealPrefixGrouping
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem rationalCircle_real_prefix (Γ : Finset ℚ) (M : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) {R : ℝ} (hR : 0 ≤ R) (F : ℚ → C(PrimeCircle,ℂ)) :
    (∑ r ∈ Γ.filter (fun r => (r.den : ℝ) ≤ R),F r)=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock Γ F) := by
  rw [realTruncatedCircleSymbol_prefix (M+1) hR]
  simpa only [intervalCircleSymbol,rationalCircleDenominatorBlock,Nat.zero_add] using
    rational_real_prefix_grouping Γ M hΓ hR F
end PrimeSquares
