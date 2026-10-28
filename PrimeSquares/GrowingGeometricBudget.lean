import PrimeSquares.DyadicGaussCollarEnergy

open Finset
namespace PrimeSquares

theorem growing_geometric_partial {r : ℝ} (hr : 1 < r) (J : ℕ) :
    (∑ s ∈ range J,r^s) ≤ r^J/(r-1) := by
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  rw [geom_sum_mul]
  linarith

theorem collar_dyadic_ratio_gt_one {δ : ℝ} (hδ : δ < 1) : 1 < (2 : ℝ)^(1-δ) := by
  have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (sub_pos.mpr hδ)
  simpa only [Real.rpow_zero] using hh

end PrimeSquares
