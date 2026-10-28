import PrimeSquares.RealOrdinaryKernelDecay
import PrimeSquares.PhysicalLowKernel

namespace PrimeSquares

noncomputable def realLowAmplitude (N : ℕ) (Q : ℝ) : ℝ :=
  lowSpatialConstant*Q*Real.log (2*Q)/(N : ℝ)^2

theorem realLowAmplitude_nonneg (N : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ realLowAmplitude N Q := by
  unfold realLowAmplitude
  exact div_nonneg (mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (by linarith))
    (Real.log_nonneg (by linarith))) (sq_nonneg _)

theorem realLowAmplitude_scale_mono {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {Q : ℝ} (hQ : 1 ≤ Q) :
    realLowAmplitude M Q ≤ realLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : (N : ℝ) ≤ M := by exact_mod_cast hNM
  unfold realLowAmplitude
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (by linarith)) (Real.log_nonneg (by linarith)))
    (sq_pos_of_pos hNp) (pow_le_pow_left₀ hNp.le hNr 2)

end PrimeSquares
