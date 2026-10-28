import PrimeSquares.RealOrdinaryAmplitudeBound
import PrimeSquares.FiniteLocalConvolution

namespace PrimeSquares

theorem realOrdinaryPhysicalKernel_local {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution (realOrdinaryPhysicalKernel N Q) F f x‖ ≤
      (4*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA : 0 ≤ lowSpatialConstant*Q*Real.log (2*Q) :=
    mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (by linarith)) (Real.log_nonneg (by linarith))
  have h := finiteConvolution_local_mass (realOrdinaryPhysicalKernel N Q) hA (sq_pos_of_pos hNp)
    (realOrdinaryPhysicalKernel_amplitude hN hQ) F f x
  convert h using 1
  ring

end PrimeSquares
