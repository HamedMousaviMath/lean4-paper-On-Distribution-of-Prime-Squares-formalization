import PrimeSquares.CircleSourceCutoffNorm
import PrimeSquares.CircleMultipliers
namespace PrimeSquares
theorem circleSourceCutoff_multiplier_norm {s : ℕ} (hs : 1 ≤ s) (r : ℚ) :
    ‖integerMultiplier (circleSourceCutoff s r)‖ ≤ 1 :=
  (integerMultiplier_opNorm_le _).trans (circleSourceCutoff_norm hs r)
end PrimeSquares
