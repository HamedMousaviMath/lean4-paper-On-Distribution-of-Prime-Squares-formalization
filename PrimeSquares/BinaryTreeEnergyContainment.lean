import PrimeSquares.BinaryTreeSquareEnergy
namespace PrimeSquares
theorem binaryTreeSquareEnergy_root (h a : ℕ) (f : ℕ → ℂ) :
    ‖intervalComplexSum a (2^h) f‖^2 ≤ binaryTreeSquareEnergy h a f := by
  cases h with
  | zero => simp only [pow_zero,intervalComplexSum_one,binaryTreeSquareEnergy,le_refl]
  | succ h =>
    change _ ≤ ‖intervalComplexSum a (2^(h+1)) f‖^2+_+_
    linarith [binaryTreeSquareEnergy_nonneg h a f,binaryTreeSquareEnergy_nonneg h (a+2^h) f]

theorem binaryTreeSquareEnergy_children (h a : ℕ) (f : ℕ → ℂ) :
    binaryTreeSquareEnergy h a f+binaryTreeSquareEnergy h (a+2^h) f ≤ binaryTreeSquareEnergy (h+1) a f := by
  change _ ≤ ‖intervalComplexSum a (2^(h+1)) f‖^2+_+_
  linarith [sq_nonneg ‖intervalComplexSum a (2^(h+1)) f‖]
end PrimeSquares
