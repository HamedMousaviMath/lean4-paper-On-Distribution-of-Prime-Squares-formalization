import PrimeSquares.DyadicPowerDecay
import Mathlib.Analysis.SpecificLimits.Normed

namespace PrimeSquares

theorem geometric_inverse_power_partial {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    (∑ s ∈ Finset.range J,((2 : ℝ)^(-ε))^s) ≤ (1-(2 : ℝ)^(-ε))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(-ε) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ)^(-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε)
  have hh := hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)^(-ε)) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)
  exact (hh.summable.sum_le_tsum (Finset.range J) (fun s _ => pow_nonneg hr0 s)).trans_eq hh.tsum_eq

theorem geometric_inverse_power_denominator_pos {ε : ℝ} (hε : 0 < ε) :
    0 < 1-(2 : ℝ)^(-ε) := by
  have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hε)
  linarith

end PrimeSquares
