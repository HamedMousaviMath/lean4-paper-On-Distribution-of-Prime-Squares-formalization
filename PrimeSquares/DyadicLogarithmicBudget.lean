import PrimeSquares.SourceRangeMonotonicity

namespace PrimeSquares

theorem two_pow_monotone {j k : ℕ} (hjk : j ≤ k) : (2 : ℕ)^j ≤ 2^k :=
  Nat.pow_le_pow_right (by decide) hjk

theorem log_two_pow_nat (j : ℕ) : Real.log (((2 : ℕ)^j : ℕ) : ℝ) = (j : ℝ)*Real.log 2 := by
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]

theorem dyadic_log_linear_lower (j : ℕ) :
    Real.log 2*((j : ℝ)+1) ≤ 1+Real.log (((2 : ℕ)^j : ℕ) : ℝ) := by
  rw [log_two_pow_nat]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem dyadic_log_inverse_power {A : ℝ} (hA : 0 ≤ A) (j : ℕ) :
    (1+Real.log (((2 : ℕ)^j : ℕ) : ℝ))^(-A) ≤
      (Real.log 2)^(-A)*((j : ℝ)+1)^(-A) := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hj : 0 < (j : ℝ)+1 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos (mul_pos hl hj) (dyadic_log_linear_lower j) (neg_nonpos.mpr hA)
  rwa [Real.mul_rpow hl.le hj.le] at h

end PrimeSquares
