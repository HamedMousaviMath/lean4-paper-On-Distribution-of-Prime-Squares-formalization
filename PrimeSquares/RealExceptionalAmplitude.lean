import PrimeSquares.RealExceptionalKernelDecay
import PrimeSquares.RealLowAmplitude
import PrimeSquares.KernelSensitiveFourierL1

namespace PrimeSquares

theorem realExceptionalPhysicalKernel_amplitude {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (x : ℤ) :
    ‖realExceptionalPhysicalKernel N q₀ χ₀ Q β M x‖ ≤ realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : 0 < Q := by linarith
  have hC := cutoffDecayConstant_nonneg 10
  have hp : 0 ≤ (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x :=
    mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ _ := realExceptionalPhysicalKernel_decay hN hQ q₀ χ₀ hχ hβ M x
    _ ≤ (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x*
        ((cohenLogConstant/2+correlationLogConstant)*Real.log (2*Q)) := by
      apply mul_le_mul_of_nonneg_left _ hp
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (div_nonneg cohenLogConstant_pos.le (by norm_num)))
        (Real.log_nonneg (by linarith))
    _ = _ := by unfold realLowAmplitude lowSpatialConstant;ring

theorem realExceptionalLowModel_kernel_uniform {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (x : ℤ) :
    ‖fourierKernel (realExceptionalLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M) x‖ ≤ realLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [realExceptionalLowModel_kernel]
  exact (realExceptionalPhysicalKernel_amplitude hN hQ q₀ χ₀ hχ hβ M x).trans
    (mul_le_of_le_one_right (realLowAmplitude_nonneg N (by linarith))
      (decayProfile_le_one (sq_pos_of_pos hNp) _ _))

theorem realExceptionalLowModel_L1_norm {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (M : ℕ) :
    ‖fourierL1Operator (realExceptionalLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M)‖ ≤ realLowAmplitude N Q :=
  fourierL1Operator_opNorm_kernel_bound _ (realExceptionalLowModel_kernel_uniform hN hQ hb q₀ χ₀ hχ hβ M)

end PrimeSquares
