import PrimeSquares.BinaryTreeIntervalDomination
open scoped lp
namespace PrimeSquares
theorem time_prefix_pointwise_envelope (h a K : ℕ) (hK : K ≤ 2^h)
    (u : ℕ → ℕ → ℤ → ℂ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2)
    (hG : ∀ t k b x,‖intervalComplexSum b (2^k) (fun i => u t i x)‖ ≤ G k b x)
    (t : ℕ) (x : ℤ) :
    ‖intervalComplexSum a K (fun i => u t i x)‖ ≤ Real.sqrt (h+1 : ℝ)*binaryNodeEnvelope h a G x := by
  have hp := binary_prefix_norm_envelope h a K (fun i => u t i x) hK
  have he := binaryTree_interval_domination h a (fun i => u t i x) (fun k b => G k b x)
    (fun k b => hG t k b x)
  exact hp.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _))
end PrimeSquares
