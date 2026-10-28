import PrimeSquares.WeightedMultiplierBudget
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
noncomputable def paddedCircleSymbols (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (i : ℕ) : C(PrimeCircle,ℂ) := if i<L then m i else 0
theorem paddedCircleSymbols_inside (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) {i : ℕ} (hi : i<L) :
    paddedCircleSymbols L m i=m i := by simp [paddedCircleSymbols,hi]
theorem paddedCircleSymbols_outside (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) {i : ℕ} (hi : L ≤ i) :
    paddedCircleSymbols L m i=0 := by simp [paddedCircleSymbols,not_lt.mpr hi]
end PrimeSquares
