import PrimeSquares.BinaryPrefixSquareBound
namespace PrimeSquares
theorem binary_prefix_norm_envelope (h a K : ℕ) (f : ℕ → ℂ) (hK : K ≤ 2^h) :
    ‖intervalComplexSum a K f‖ ≤ Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryTreeSquareEnergy h a f) := by
  have hb := binary_prefix_square_bound h a K f hK
  have hn := binaryTreeSquareEnergy_nonneg h a f
  have hs : (Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryTreeSquareEnergy h a f))^2=
      (h+1 : ℝ)*binaryTreeSquareEnergy h a f := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hn]
  have hp : 0 ≤ Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryTreeSquareEnergy h a f) := by positivity
  nlinarith [norm_nonneg (intervalComplexSum a K f)]
end PrimeSquares
