import PrimeSquares.BinaryPrefixSplit
namespace PrimeSquares
noncomputable def binaryTreeSquareEnergy : ℕ → ℕ → (ℕ → ℂ) → ℝ
  | 0,a,f => ‖f a‖^2
  | h+1,a,f => ‖intervalComplexSum a (2^(h+1)) f‖^2+
      binaryTreeSquareEnergy h a f+binaryTreeSquareEnergy h (a+2^h) f
theorem binaryTreeSquareEnergy_nonneg (h a : ℕ) (f : ℕ → ℂ) : 0 ≤ binaryTreeSquareEnergy h a f := by
  induction h generalizing a with
  | zero => exact sq_nonneg _
  | succ h ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih a)) (ih _)
end PrimeSquares
