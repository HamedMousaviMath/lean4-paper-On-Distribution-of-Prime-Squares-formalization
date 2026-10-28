import PrimeSquares.WeightedPowerFiniteTail

open Finset
namespace PrimeSquares

theorem weighted_power_shift_summable {s : ℝ} (hs : 2 ≤ s) (J : ℕ) :
    Summable (fun j : ℕ => ((J+j : ℕ)+1 : ℝ)^(-s)) := by
  apply summable_of_sum_range_le (fun j => Real.rpow_nonneg (by positivity) _)
  intro K
  rw [sum_range_shift_eq_Ico (fun j => ((j : ℝ)+1)^(-s)) J K]
  exact weighted_power_finite_tail hs J (J+K)

theorem weighted_power_infinite_tail {s : ℝ} (hs : 2 ≤ s) (J : ℕ) :
    (∑' j : ℕ, ((J+j : ℕ)+1 : ℝ)^(-s)) ≤ 2*((J : ℝ)+1)^(1-s) := by
  apply Real.tsum_le_of_sum_range_le (fun j => Real.rpow_nonneg (by positivity) _)
  intro K
  rw [sum_range_shift_eq_Ico (fun j => ((j : ℝ)+1)^(-s)) J K]
  exact weighted_power_finite_tail hs J (J+K)

end PrimeSquares
