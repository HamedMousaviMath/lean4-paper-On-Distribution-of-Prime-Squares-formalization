import PrimeSquares.MajorArcParameters

namespace PrimeSquares

theorem sourceQCoefficient_pos {c : ℝ} (hc : 0 < c) : 0 < min (c/7) 1/8 := by
  exact div_pos (lt_min (by positivity) (by norm_num)) (by norm_num)

theorem sourceQRange_upward {N M Q c : ℝ} (hc : 0 < c) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hQ : Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N)) :
    Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log M) := by
  exact hQ.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hNM)) (sourceQCoefficient_pos hc).le)

theorem sourceMajorArcScale_mono_N {N M : ℝ} (hN : 1 ≤ N) (hNM : N ≤ M) (Q : ℝ) :
    sourceMajorArcScale N Q ≤ sourceMajorArcScale M Q := by
  apply max_le_max _ le_rfl
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow (Real.log_nonneg hN)
    (Real.log_le_log (by linarith) hNM) (by norm_num)

end PrimeSquares
