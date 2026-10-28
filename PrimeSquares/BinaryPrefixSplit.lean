import PrimeSquares.IntervalComplexSum
namespace PrimeSquares
theorem intervalComplexSum_binary_prefix (h a K : ℕ) (f : ℕ → ℂ) (hK : 2^h < K) :
    intervalComplexSum a K f=intervalComplexSum a (2^h) f+intervalComplexSum (a+2^h) (K-2^h) f := by
  have he : K=2^h+(K-2^h) := by omega
  conv_lhs => rw [he]
  exact intervalComplexSum_add a _ _ f
theorem binary_prefix_remainder {h K : ℕ} (hK : K ≤ 2^(h+1)) : K-2^h ≤ 2^h := by
  rw [pow_succ] at hK
  omega
end PrimeSquares
