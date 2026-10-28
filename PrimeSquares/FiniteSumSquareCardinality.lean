import PrimeSquares.WeightedCircleCollarMaximum
import PrimeSquares.DyadicActiveBound

open Finset
namespace PrimeSquares

theorem norm_finset_sum_square_card {ι : Type*} (S : Finset ι) (F : ι → ℂ) :
    ‖∑ i ∈ S,F i‖^2 ≤ (S.card : ℝ)*(∑ i ∈ S,‖F i‖^2) := by
  have hc : (∑ i ∈ S,‖F i‖)^2 ≤ (∑ i ∈ S,‖F i‖^2)*(S.card : ℝ) := by
    simpa only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one] using
      sum_mul_sq_le_sq_mul_sq S (fun i => ‖F i‖) (fun _ => (1 : ℝ))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S F) 2
  simpa only [mul_comm] using hh.trans hc

end PrimeSquares
