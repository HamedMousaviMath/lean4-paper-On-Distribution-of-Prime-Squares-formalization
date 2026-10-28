import PrimeSquares.RealLowAmplitude

namespace PrimeSquares

theorem realOrdinaryPhysicalKernel_amplitude {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q) (x : ℤ) :
    ‖realOrdinaryPhysicalKernel N Q x‖ ≤ realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : 0 < Q := by linarith
  have hC := cutoffDecayConstant_nonneg 10
  have hp : 0 ≤ (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x :=
    mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ _ := realOrdinaryPhysicalKernel_decay hN hQ x
    _ ≤ (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x*
        ((cohenLogConstant/2+correlationLogConstant)*Real.log (2*Q)) := by
      apply mul_le_mul_of_nonneg_left _ hp
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right correlationLogConstant_pos.le)
        (Real.log_nonneg (by linarith))
    _ = _ := by unfold realLowAmplitude lowSpatialConstant;ring

theorem realOrdinaryPhysicalKernel_uniform {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q) (x : ℤ) :
    ‖realOrdinaryPhysicalKernel N Q x‖ ≤ realLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact (realOrdinaryPhysicalKernel_amplitude hN hQ x).trans
    (mul_le_of_le_one_right (realLowAmplitude_nonneg N (by linarith))
      (decayProfile_le_one (sq_pos_of_pos hNp) _ _))

end PrimeSquares
