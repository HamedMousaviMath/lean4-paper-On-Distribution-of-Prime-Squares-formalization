import PrimeSquares.RealOrdinaryLocalMass
import PrimeSquares.RealOrdinaryL1Bound

namespace PrimeSquares

theorem realOrdinaryLowModel_finite_convolution {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    integerMultiplier (realOrdinaryLowModel N (by omega) Q (by linarith) hb) (finiteInputLp F f 2) x=
      finiteConvolution (realOrdinaryPhysicalKernel N Q) F f x := by
  rw [integerMultiplier_finite_convolution]
  unfold finiteConvolution
  apply Finset.sum_congr rfl
  intro y _
  rw [realOrdinaryLowModel_kernel]

theorem realOrdinaryLowModel_local {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖integerMultiplier (realOrdinaryLowModel N (by omega) Q (by linarith) hb) (finiteInputLp F f 2) x‖ ≤
      (4*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  rw [realOrdinaryLowModel_finite_convolution hN hQ hb]
  exact realOrdinaryPhysicalKernel_local hN hQ F f x

end PrimeSquares
