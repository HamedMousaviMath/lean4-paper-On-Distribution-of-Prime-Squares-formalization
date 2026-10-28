import PrimeSquares.TwoTermWeightedSquare
namespace PrimeSquares
theorem binary_prefix_square_bound (h a K : ℕ) (f : ℕ → ℂ) (hK : K ≤ 2^h) :
    ‖intervalComplexSum a K f‖^2 ≤ (h+1 : ℝ)*binaryTreeSquareEnergy h a f := by
  induction h generalizing a K with
  | zero =>
    have hk : K=0 ∨ K=1 := by norm_num at hK;omega
    rcases hk with rfl|rfl
    · simpa [intervalComplexSum_zero] using binaryTreeSquareEnergy_nonneg 0 a f
    · simp only [intervalComplexSum_one,binaryTreeSquareEnergy,Nat.cast_zero,zero_add,one_mul,le_refl]
  | succ h ih =>
    have hc := binaryTreeSquareEnergy_children h a f
    have hl := binaryTreeSquareEnergy_nonneg h a f
    have hr := binaryTreeSquareEnergy_nonneg h (a+2^h) f
    have ht := binaryTreeSquareEnergy_nonneg (h+1) a f
    by_cases hk : K ≤ 2^h
    · have hi := ih a K hk
      have hleft : binaryTreeSquareEnergy h a f ≤ binaryTreeSquareEnergy (h+1) a f := by linarith
      have hm := mul_le_mul_of_nonneg_left hleft (show (0 : ℝ) ≤ h+1 by positivity)
      push_cast
      nlinarith
    · have hk' : 2^h < K := lt_of_not_ge hk
      rw [intervalComplexSum_binary_prefix h a K f hk']
      have hi := ih (a+2^h) (K-2^h) (binary_prefix_remainder hK)
      have hw := norm_add_square_weighted (intervalComplexSum a (2^h) f)
        (intervalComplexSum (a+2^h) (K-2^h) f) (by positivity : (0 : ℝ) < h+1) hi
      have hb := binaryTreeSquareEnergy_root h a f
      have hm := mul_le_mul_of_nonneg_left (show ‖intervalComplexSum a (2^h) f‖^2+
          binaryTreeSquareEnergy h (a+2^h) f ≤ binaryTreeSquareEnergy (h+1) a f by linarith)
        (show (0 : ℝ) ≤ (h+1)+1 by positivity)
      push_cast
      exact hw.trans hm
end PrimeSquares
