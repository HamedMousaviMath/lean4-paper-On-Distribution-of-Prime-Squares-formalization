import PrimeSquares.ActualPositiveSquareFamilies
import PrimeSquares.IWTransitionScale
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
namespace PrimeSquares

theorem real_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2*Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

theorem primeCounting_positive_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 < Nat.primeCounting N := by
  by_contra hz
  have hzero : Nat.primeCounting N = 0 := by omega
  have hsmall := (Nat.primeCounting_eq_zero_iff).mp hzero
  omega

theorem primeCounting_log_lower_bound {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ≤ 512*(Nat.primeCounting N : ℝ)*Real.log (N : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hhalf : (1/2 : ℝ) ≤ Real.log (N : ℝ) :=
    real_log_two_half_le.trans (Real.log_le_log (by norm_num) hNr)
  have hpi : (1 : ℝ) ≤ Nat.primeCounting N := by
    exact_mod_cast primeCounting_positive_of_two_le hN
  by_cases hlarge : 256 ≤ N
  · have hlargeR : (256 : ℝ) ≤ N := by exact_mod_cast hlarge
    have hs : 16 ≤ Real.sqrt (N : ℝ) := by
      calc
        16 = Real.sqrt (256 : ℝ) := by
          rw [show (256 : ℝ) = 16^2 by norm_num, Real.sqrt_sq_eq_abs]
          norm_num
        _ ≤ _ := Real.sqrt_le_sqrt hlargeR
    have hs0 := Real.sqrt_nonneg (N : ℝ)
    have hs2 := Real.sq_sqrt hNp.le
    have hpoly := mul_nonneg (show 0 ≤ Real.sqrt (N : ℝ)-16 by linarith)
      (show 0 ≤ Real.sqrt (N : ℝ)+8 by linarith)
    have hlogN := real_log_le_two_sqrt hNp
    have hlogNext : Real.log ((N : ℝ)+1) ≤ 1+2*Real.sqrt (N : ℝ) := by
      have h := Real.log_le_log (by positivity : 0 < (N : ℝ)+1)
        (show (N : ℝ)+1 ≤ 2*(N : ℝ) by linarith)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNp.ne'] at h
      have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hquarter : Real.log ((N : ℝ)+1) ≤ (N : ℝ)/4 := by nlinarith
    have hCheb := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge N)
    have hm := mul_le_mul_of_nonneg_left real_log_two_half_le hNp.le
    have hbase : (N : ℝ)/4 ≤ (Nat.primeCounting N : ℝ)*Real.log (N : ℝ) := by
      nlinarith
    nlinarith
  · have hsmall : (N : ℝ) < 256 := by exact_mod_cast (show N < 256 by omega)
    have hprod := mul_le_mul hpi hhalf (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith : (0 : ℝ) ≤ Nat.primeCounting N)
    nlinarith

theorem primeCounting_inverse_bound {N : ℕ} (hN : 2 ≤ N) :
    ((Nat.primeCounting N : ℝ)⁻¹) ≤ 512*Real.log (N : ℝ)/(N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpi : (0 : ℝ) < Nat.primeCounting N := by exact_mod_cast primeCounting_positive_of_two_le hN
  apply (le_div_iff₀ hNp).mpr
  apply (inv_mul_le_iff₀ hpi).mpr
  nlinarith [primeCounting_log_lower_bound hN]

end PrimeSquares
