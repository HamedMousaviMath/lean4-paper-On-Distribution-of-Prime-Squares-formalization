import PrimeSquares.PrefixL2MajorantNorm
open Finset
namespace PrimeSquares
noncomputable def intervalRealBudget (a K : ℕ) (w : ℕ → ℝ) : ℝ := ∑ i ∈ range K,w (a+i)
theorem intervalRealBudget_add (a L K : ℕ) (w : ℕ → ℝ) :
    intervalRealBudget a (L+K) w=intervalRealBudget a L w+intervalRealBudget (a+L) K w := by
  simp only [intervalRealBudget,sum_range_add,Nat.add_assoc]
theorem intervalRealBudget_nonneg (a K : ℕ) (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i) : 0 ≤ intervalRealBudget a K w :=
  sum_nonneg (fun i _ => hw (a+i))
end PrimeSquares
