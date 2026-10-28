import PrimeSquares.BinaryNodeEnvelopeNorm
namespace PrimeSquares
theorem binaryTree_interval_domination (h a : ℕ) (f : ℕ → ℂ) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k b,‖intervalComplexSum b (2^k) f‖ ≤ v k b) :
    binaryTreeSquareEnergy h a f ≤ binaryNodeSquareEnergy h a v := by
  induction h generalizing a with
  | zero =>
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hv 0 a) 2
    simpa only [pow_zero,intervalComplexSum_one,binaryTreeSquareEnergy,binaryNodeSquareEnergy] using hh
  | succ h ih =>
    exact add_le_add (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hv (h+1) a) 2) (ih a)) (ih (a+2^h))
end PrimeSquares
