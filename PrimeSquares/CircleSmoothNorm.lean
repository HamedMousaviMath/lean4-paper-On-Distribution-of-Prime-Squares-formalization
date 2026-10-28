import PrimeSquares.CircleSmoothPointwiseBound
import PrimeSquares.CircleMultipliers
namespace PrimeSquares
theorem circleSmoothCutoff_norm {a : ℝ} (ha : 1 ≤ a) (h4 : 4 ≤ a) (r : ℚ) :
    ‖circleSmoothCutoff a ha r‖ ≤ 1 :=
  (ContinuousMap.norm_le _ (by norm_num)).mpr (circleSmoothCutoff_pointwise_norm ha h4 r)
theorem circleSmoothCutoff_multiplier_norm {a : ℝ} (ha : 1 ≤ a) (h4 : 4 ≤ a) (r : ℚ) :
    ‖integerMultiplier (circleSmoothCutoff a ha r)‖ ≤ 1 :=
  (integerMultiplier_opNorm_le _).trans (circleSmoothCutoff_norm ha h4 r)
end PrimeSquares
