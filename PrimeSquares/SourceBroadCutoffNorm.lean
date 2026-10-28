import PrimeSquares.DyadicSparseSquareEnergy

namespace PrimeSquares

theorem sourceBroadCutoff_complex_norm (s : ℕ) (θ : ℝ) :
    ‖Complex.ofReal (sourceArcCutoffScale s θ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact sourceArcCutoff_le_one _

theorem sourceBroadCutoff_mul_norm (c : ℂ) (s : ℕ) (θ : ℝ) :
    ‖c*Complex.ofReal (sourceArcCutoffScale s θ)‖ ≤ ‖c‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (sourceBroadCutoff_complex_norm s θ) (norm_nonneg c)).trans (by simp)

end PrimeSquares
