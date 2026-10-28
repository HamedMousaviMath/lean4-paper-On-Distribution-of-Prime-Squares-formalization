import PrimeSquares.IntervalL2Sum
open scoped lp
namespace PrimeSquares
noncomputable def binaryTreeL2Energy : ℕ → ℕ → (ℕ → ℓ²(ℤ,ℂ)) → ℝ
  | 0,a,F => ‖F a‖^2
  | h+1,a,F => ‖intervalL2Sum a (2^(h+1)) F‖^2+binaryTreeL2Energy h a F+binaryTreeL2Energy h (a+2^h) F
theorem binaryTreeL2Energy_nonneg (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) : 0 ≤ binaryTreeL2Energy h a F := by
  induction h generalizing a with
  | zero => exact sq_nonneg _
  | succ h ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih a)) (ih _)
end PrimeSquares
