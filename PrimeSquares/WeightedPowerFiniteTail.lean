import PrimeSquares.ReciprocalSquareInfiniteTail

open Finset
namespace PrimeSquares

theorem weighted_power_reciprocal_bound {s : ℝ} (hs : 2 ≤ s) {J j : ℕ} (hJj : J ≤ j) :
    ((j : ℝ)+1)^(-s) ≤ ((J : ℝ)+1)^(2-s)*(1/((j : ℝ)+1)^2) := by
  have hJ : (0 : ℝ) < (J : ℝ)+1 := by positivity
  have hj : (0 : ℝ) < (j : ℝ)+1 := by positivity
  have hbase : (J : ℝ)+1 ≤ (j : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hJj 1
  have hpow := Real.rpow_le_rpow_of_nonpos hJ hbase
    (by linarith : 2-s ≤ 0)
  have he : ((j : ℝ)+1)^(-s) = ((j : ℝ)+1)^(2-s)*(1/((j : ℝ)+1)^2) := by
    have hi : (1 : ℝ)/((j : ℝ)+1)^2 = ((j : ℝ)+1)^(-2 : ℝ) := by
      rw [Real.rpow_neg hj.le]
      norm_num
    rw [hi,←Real.rpow_add hj]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

theorem weighted_power_finite_tail {s : ℝ} (hs : 2 ≤ s) (J K : ℕ) :
    (∑ j ∈ Ico J K, ((j : ℝ)+1)^(-s)) ≤ 2*((J : ℝ)+1)^(1-s) := by
  have hJ : (0 : ℝ) < (J : ℝ)+1 := by positivity
  calc
    _ ≤ ∑ j ∈ Ico J K, ((J : ℝ)+1)^(2-s)*(1/((j : ℝ)+1)^2) :=
      sum_le_sum (fun j hj => weighted_power_reciprocal_bound hs (mem_Ico.mp hj).1)
    _ = ((J : ℝ)+1)^(2-s)*(∑ j ∈ Ico J K, (1 : ℝ)/((j : ℝ)+1)^2) := (mul_sum ..).symm
    _ ≤ ((J : ℝ)+1)^(2-s)*(2/((J : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_finite_tail J K) (Real.rpow_nonneg hJ.le _)
    _ = 2*((J : ℝ)+1)^(1-s) := by
      calc
        _ = 2*(((J : ℝ)+1)^(2-s)/((J : ℝ)+1)) := by ring
        _ = 2*((J : ℝ)+1)^((2-s)-1) := by rw [Real.rpow_sub hJ (2-s) 1,Real.rpow_one]
        _ = _ := by congr 2;ring

end PrimeSquares
