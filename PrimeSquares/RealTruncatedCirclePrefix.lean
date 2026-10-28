import PrimeSquares.FiniteDisjointPrefixMaximum
import PrimeSquares.RealDenominatorPrefixSet
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
noncomputable def realTruncatedCircleSymbol (L : ℕ) (R : ℝ)
    (m : ℕ → C(PrimeCircle,ℂ)) : C(PrimeCircle,ℂ) :=
  ∑ i ∈ range L,if (i : ℝ) ≤ R then m i else 0
theorem realTruncatedCircleSymbol_prefix (L : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ → C(PrimeCircle,ℂ)) :
    realTruncatedCircleSymbol L R m=intervalCircleSymbol 0 (min L (⌊R⌋₊+1)) m := by
  unfold realTruncatedCircleSymbol intervalCircleSymbol
  rw [←real_denominator_prefix_filter L hR,sum_filter]
  simp only [Nat.zero_add]
end PrimeSquares
