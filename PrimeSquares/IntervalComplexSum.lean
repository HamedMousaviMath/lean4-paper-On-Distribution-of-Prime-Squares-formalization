import PrimeSquares.CommonTailMaskCounterexample
open Finset
namespace PrimeSquares
noncomputable def intervalComplexSum (a K : ℕ) (f : ℕ → ℂ) : ℂ := ∑ i ∈ range K,f (a+i)
theorem intervalComplexSum_add (a L K : ℕ) (f : ℕ → ℂ) :
    intervalComplexSum a (L+K) f=intervalComplexSum a L f+intervalComplexSum (a+L) K f := by
  simp only [intervalComplexSum,sum_range_add,Nat.add_assoc]
theorem intervalComplexSum_zero (a : ℕ) (f : ℕ → ℂ) : intervalComplexSum a 0 f=0 := by
  simp only [intervalComplexSum,range_zero,sum_empty]
theorem intervalComplexSum_one (a : ℕ) (f : ℕ → ℂ) : intervalComplexSum a 1 f=f a := by
  simp only [intervalComplexSum,sum_range_one,Nat.add_zero]
end PrimeSquares
