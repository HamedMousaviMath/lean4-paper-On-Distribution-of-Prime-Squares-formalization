import PrimeSquares.PaddedSymbolDisjointness
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem paddedCircleSymbols_prefix (L K : ℕ) (hK : K ≤ L) (m : ℕ → C(PrimeCircle,ℂ)) :
    intervalCircleSymbol 0 K (paddedCircleSymbols L m)=intervalCircleSymbol 0 K m := by
  unfold intervalCircleSymbol
  apply sum_congr rfl
  intro i hi
  simp only [Nat.zero_add]
  exact paddedCircleSymbols_inside L m (lt_of_lt_of_le (mem_range.mp hi) hK)
end PrimeSquares
