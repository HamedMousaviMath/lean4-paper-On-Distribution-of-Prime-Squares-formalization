import PrimeSquares.PaddedPrefixIdentity
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem paddedMultiplier_square_budget (L T : ℕ) (hLT : L ≤ T)
    (m : ℕ → C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ)) :
    intervalRealBudget 0 T (fun i => ‖integerMultiplier (paddedCircleSymbols L m i) f‖^2)=
      ∑ i ∈ range L,‖integerMultiplier (m i) f‖^2 := by
  unfold intervalRealBudget
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ range L,‖integerMultiplier (paddedCircleSymbols L m i) f‖^2 := by
      symm
      apply sum_subset (range_mono hLT)
      intro i _ hi
      have hLi : L ≤ i := by simpa only [mem_range,not_lt] using hi
      simp [paddedCircleSymbols_outside L m hLi,integerMultiplier_zero]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      rw [paddedCircleSymbols_inside L m (mem_range.mp hi)]
end PrimeSquares
