import PrimeSquares.IntervalCircleSymbol
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem integerMultiplier_finset_sum {ι : Type*} (S : Finset ι) (m : ι → C(PrimeCircle,ℂ)) :
    integerMultiplier (∑ i ∈ S,m i)=∑ i ∈ S,integerMultiplier (m i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [integerMultiplier_zero]
  | @insert i S hi ih => simp only [sum_insert hi,integerMultiplier_add,ih]
theorem integerMultiplier_interval (a K : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ)) :
    integerMultiplier (intervalCircleSymbol a K m) f=
      intervalL2Sum a K (fun i => integerMultiplier (m i) f) := by
  simp only [intervalCircleSymbol,integerMultiplier_finset_sum,_root_.sum_apply,intervalL2Sum]
end PrimeSquares
