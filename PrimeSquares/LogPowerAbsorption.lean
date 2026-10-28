import PrimeSquares.SourceModelLogarithmicRate

open Filter
namespace PrimeSquares

theorem eventually_log_rpow_le_rpow (k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, (Real.log R)^k ≤ R^ε := by
  have h := (isLittleO_log_rpow_rpow_atTop k hε).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),h] with R hR hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hR) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ R) _),one_mul] using hh

theorem eventually_scaled_rpow_le_rpow {K a b : ℝ} (hK : 0 ≤ K) (hab : a < b) :
    ∀ᶠ R : ℝ in atTop, K*R^a ≤ R^b := by
  have hp := eventually_rpow_le_mul_rpow hab (inv_pos.mpr (by linarith : 0 < K+1))
  filter_upwards [eventually_gt_atTop (0 : ℝ),hp] with R hR hh
  have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ K+1)
  rw [←mul_assoc,mul_inv_cancel₀ (by linarith : K+1 ≠ 0),one_mul] at hm
  exact (mul_le_mul_of_nonneg_right (by linarith : K ≤ K+1) (Real.rpow_nonneg hR.le _)).trans hm

theorem eventually_two_rpow_budget {K L a d b : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hab : a < b) (hdb : d < b) :
    ∀ᶠ R : ℝ in atTop, K*R^a+L*R^d ≤ R^b := by
  filter_upwards [eventually_scaled_rpow_le_rpow (by linarith : 0 ≤ 2*K) hab,
    eventually_scaled_rpow_le_rpow (by linarith : 0 ≤ 2*L) hdb] with R h₁ h₂
  nlinarith only [h₁,h₂]

end PrimeSquares
