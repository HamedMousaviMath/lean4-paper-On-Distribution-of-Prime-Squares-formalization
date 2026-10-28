import PrimeSquares.CircleTimePrefixPairing
import PrimeSquares.RationalDenominatorGrouping
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
noncomputable def rationalCircleDenominatorBlock (Γ : Finset ℚ) (F : ℚ → C(PrimeCircle,ℂ))
    (q : ℕ) : C(PrimeCircle,ℂ) := ∑ r ∈ Γ.filter (fun r => r.den=q),F r
theorem rationalCircle_full_blocks (Γ : Finset ℚ) (M : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) (F : ℚ → C(PrimeCircle,ℂ)) :
    (∑ r ∈ Γ,F r)=intervalCircleSymbol 0 (M+1) (rationalCircleDenominatorBlock Γ F) := by
  simpa only [intervalCircleSymbol,rationalCircleDenominatorBlock,Nat.zero_add] using
    rational_denominator_grouping Γ M hΓ F
end PrimeSquares
