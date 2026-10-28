import PrimeSquares.ReciprocalSquareFiniteTail

open Finset
namespace PrimeSquares

theorem sum_range_shift_eq_Ico (f : ℕ → ℝ) (J K : ℕ) :
    (∑ j ∈ range K, f (J+j)) = ∑ j ∈ Ico J (J+K), f j := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

theorem reciprocal_square_shift_summable (J : ℕ) :
    Summable (fun j : ℕ => (1 : ℝ)/((J+j : ℕ)+1 : ℝ)^2) := by
  apply summable_of_sum_range_le (fun j => by positivity)
  intro K
  rw [sum_range_shift_eq_Ico (fun j => (1 : ℝ)/((j : ℝ)+1)^2) J K]
  exact reciprocal_square_finite_tail J (J+K)

theorem reciprocal_square_infinite_tail (J : ℕ) :
    (∑' j : ℕ, (1 : ℝ)/((J+j : ℕ)+1 : ℝ)^2) ≤ 2/((J : ℝ)+1) := by
  apply Real.tsum_le_of_sum_range_le (fun j => by positivity)
  intro K
  rw [sum_range_shift_eq_Ico (fun j => (1 : ℝ)/((j : ℝ)+1)^2) J K]
  exact reciprocal_square_finite_tail J (J+K)

end PrimeSquares
