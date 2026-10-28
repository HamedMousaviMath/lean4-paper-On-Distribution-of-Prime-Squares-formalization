import PrimeSquares.LogPowerAbsorption
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals

open Finset
namespace PrimeSquares

theorem reciprocal_square_step (j : ℕ) :
    (1 : ℝ)/((j : ℝ)+1)^2 ≤ 2*(1/((j : ℝ)+1)-1/((j : ℝ)+2)) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  nlinarith

theorem reciprocal_step_sum {J K : ℕ} (hJK : J ≤ K) :
    (∑ j ∈ Ico J K, ((1 : ℝ)/((j : ℝ)+1)-1/((j : ℝ)+2))) =
      1/((J : ℝ)+1)-1/((K : ℝ)+1) := by
  induction K,hJK using Nat.le_induction with
  | base => simp
  | succ K hJK ih =>
    rw [sum_Ico_succ_top hJK,ih]
    push_cast
    ring

theorem reciprocal_square_finite_tail (J K : ℕ) :
    (∑ j ∈ Ico J K, (1 : ℝ)/((j : ℝ)+1)^2) ≤ 2/((J : ℝ)+1) := by
  by_cases hJK : J ≤ K
  · calc
      _ ≤ ∑ j ∈ Ico J K, 2*(1/((j : ℝ)+1)-1/((j : ℝ)+2)) :=
        sum_le_sum (fun j _ => reciprocal_square_step j)
      _ = 2*(1/((J : ℝ)+1)-1/((K : ℝ)+1)) := by
        rw [←mul_sum,reciprocal_step_sum hJK]
      _ ≤ _ := by
        have hk : 0 ≤ (1 : ℝ)/((K : ℝ)+1) := by positivity
        calc
          _ ≤ 2*(1/((J : ℝ)+1)) := mul_le_mul_of_nonneg_left (sub_le_self _ hk) (by norm_num)
          _ = _ := by ring
  · have he : Ico J K = ∅ := Ico_eq_empty_of_le (le_of_not_ge hJK)
    simp only [he,sum_empty]
    positivity

end PrimeSquares
