import PrimeSquares.CorrelationWeightedHarmonic

namespace PrimeSquares

noncomputable def correlationLogConstant : ℝ := Real.exp 2*(1+1/Real.log 2)

theorem correlationLogConstant_pos : 0 < correlationLogConstant := by
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold correlationLogConstant
  positivity

theorem one_add_log_le_log_twice {D : ℝ} (hD : 1 ≤ D) :
    1+Real.log D ≤ (1+1/Real.log 2)*Real.log (2*D) := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hDp : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hlog : Real.log 2 ≤ Real.log (2*D) := Real.log_le_log (by norm_num) (by linarith)
  have hone : 1 ≤ (1/Real.log 2)*Real.log (2*D) := by
    have h := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr h2.le)
    simpa only [one_div,inv_mul_cancel₀ h2.ne'] using h
  have hbase : Real.log D ≤ Real.log (2*D) := Real.log_le_log hDp (by linarith)
  nlinarith

theorem conductorCorrelationProduct_weighted_log (D : ℕ) (hD : 1 ≤ D) :
    (∑ n ∈ Finset.Icc 1 D,conductorCorrelationProduct n/(n : ℝ)) ≤
      correlationLogConstant*Real.log (2*(D : ℝ)) := by
  calc
    _ ≤ Real.exp 2*(harmonic D : ℝ) := conductorCorrelationProduct_weighted_harmonic D
    _ ≤ Real.exp 2*(1+Real.log (D : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Real.exp_pos _).le
    _ ≤ Real.exp 2*((1+1/Real.log 2)*Real.log (2*(D : ℝ))) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_log_twice (by exact_mod_cast hD)) (Real.exp_pos _).le
    _ = _ := by unfold correlationLogConstant;ring

end PrimeSquares
