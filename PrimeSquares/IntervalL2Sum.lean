import PrimeSquares.L2PointwiseMagnitude
open Finset
open scoped lp
namespace PrimeSquares
noncomputable def intervalL2Sum (a K : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) : ℓ²(ℤ,ℂ) := ∑ i ∈ range K,F (a+i)
theorem intervalL2Sum_apply (a K : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (x : ℤ) :
    intervalL2Sum a K F x=intervalComplexSum a K (fun i => F i x) := by
  simp only [intervalL2Sum,intervalComplexSum,lp.coeFn_sum,Finset.sum_apply]
theorem intervalL2Sum_add (a L K : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    intervalL2Sum a (L+K) F=intervalL2Sum a L F+intervalL2Sum (a+L) K F := by
  simp only [intervalL2Sum,sum_range_add,Nat.add_assoc]
end PrimeSquares
