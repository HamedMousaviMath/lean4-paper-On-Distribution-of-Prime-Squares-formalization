import PrimeSquares.RealOrdinaryAmplitudeBound
import PrimeSquares.KernelSensitiveFourierL1

open scoped lp
namespace PrimeSquares

theorem realOrdinaryLowModel_kernel_uniform {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (x : ℤ) :
    ‖fourierKernel (realOrdinaryLowModel N (by omega) Q (by linarith) hb) x‖ ≤ realLowAmplitude N Q := by
  rw [realOrdinaryLowModel_kernel]
  exact realOrdinaryPhysicalKernel_uniform hN hQ x

theorem realOrdinaryLowModel_L1_norm {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) :
    ‖fourierL1Operator (realOrdinaryLowModel N (by omega) Q (by linarith) hb)‖ ≤ realLowAmplitude N Q :=
  fourierL1Operator_opNorm_kernel_bound _ (realOrdinaryLowModel_kernel_uniform hN hQ hb)

theorem realOrdinaryLowModel_L1_bound {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (f : ℓ¹(ℤ, ℂ)) :
    ‖fourierL1Operator (realOrdinaryLowModel N (by omega) Q (by linarith) hb) f‖ ≤ realLowAmplitude N Q*‖f‖ :=
  fourierL1Operator_kernel_bound _ (realOrdinaryLowModel_kernel_uniform hN hQ hb) f

end PrimeSquares
