import PrimeSquares.CircleSourceCutoffPointwiseBound
namespace PrimeSquares
theorem circleSourceCutoff_norm {s : ℕ} (hs : 1 ≤ s) (r : ℚ) :
    ‖circleSourceCutoff s r‖ ≤ 1 := by
  exact (ContinuousMap.norm_le _ (by norm_num)).mpr (circleSourceCutoff_pointwise_norm hs r)
end PrimeSquares
