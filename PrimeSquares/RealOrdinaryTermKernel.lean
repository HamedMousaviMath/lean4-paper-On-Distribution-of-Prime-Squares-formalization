import PrimeSquares.RealOrdinaryCircleTerm
import PrimeSquares.CorrelationPhaseSums
import PrimeSquares.FourierKernelSums

namespace PrimeSquares

theorem realOrdinaryCircleTerm_kernel (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q : ℕ) [NeZero q] (x : ℤ) :
    fourierKernel (realOrdinaryCircleTerm N hN Q hQ hb q) x=
      normalizedCohenCorrelation q x*smoothedAnnularKernel N 1 (ordinaryLowWidth N Q q) x := by
  simp only [realOrdinaryCircleTerm,dite_eq_right (NeZero.ne q)]
  rw [fourierKernel_sum]
  simp_rw [fourierKernel_smul,circleFrequencyShift_real_kernel,circleAnnularCutoff_kernel,←mul_assoc]
  rw [←Finset.sum_mul,normalizedCohenCorrelation_phase_sum]

end PrimeSquares
