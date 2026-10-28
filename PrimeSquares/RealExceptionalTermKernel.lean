import PrimeSquares.RealExceptionalCircleTerm
import PrimeSquares.CorrelationPhaseSums
import PrimeSquares.FourierKernelSums

namespace PrimeSquares

theorem realExceptionalCircleTerm_kernel (N : ℕ) (hN : 1 ≤ N) (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (x : ℤ) :
    fourierKernel (realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β (q₀*d)) x=
      inducedIntegerCorrelation q₀ χ₀ d x*smoothedAnnularKernel N β (exceptionalLowWidth N Q (conductorMajorant q₀) d) x := by
  rw [realExceptionalCircleTerm_dvd N hN q₀ χ₀ hQ hb β (q₀*d) (Nat.dvd_mul_right q₀ d)]
  rw [fourierKernel_sum]
  simp_rw [fourierKernel_smul,circleFrequencyShift_real_kernel,circleAnnularCutoff_kernel,←mul_assoc]
  rw [←Finset.sum_mul,twistedCorrelation_phase_sum,←inducedIntegerCorrelation_eq]
  rw [Nat.mul_div_cancel_left d (NeZero.pos q₀)]

end PrimeSquares
