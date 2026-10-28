import PrimeSquares.GhoshBalancedBound
import PrimeSquares.SourceScaleFourthPower

namespace PrimeSquares

noncomputable def ghoshSourceConstant (B : ℝ) : ℝ := B*(3 : ℝ)^(1/4 : ℝ)/2

theorem ghoshSourceConstant_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ ghoshSourceConstant B := by
  dsimp [ghoshSourceConstant]
  positivity

theorem annularMangoldt_Ghosh_scale_bound {N : ℕ} (hN : 1 ≤ N)
    (ξ : ℝ) {B q R : ℝ} (hB : 0 ≤ B) (hR : 0 < R) (hpow : R^4 ≤ (N : ℝ)/2)
    (hql : ((N : ℝ)/2)^(1/2 : ℝ) ≤ q)
    (hqu : q ≤ ((N : ℝ)/2)^(3/2 : ℝ))
    (hGhosh : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤ B*((N : ℝ)/2)^(17/16 : ℝ)*
      (ghoshQuadraticBracket ((N : ℝ)/2) q)^(1/4 : ℝ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      ghoshSourceConstant B*R^(-(1/4 : ℝ)) := by
  have hp := inverse_rpow_from_fourth_power hR (by norm_num : (0 : ℝ) ≤ 1/16) hpow
  norm_num at hp
  exact (annularMangoldt_Ghosh_balanced hN ξ hB hql hqu hGhosh).trans
    (mul_le_mul_of_nonneg_left hp (ghoshSourceConstant_nonneg hB))

end PrimeSquares
