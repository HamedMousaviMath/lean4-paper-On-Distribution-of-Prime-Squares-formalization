import PrimeSquares.RealCombinedLowBounds
import PrimeSquares.RealExceptionalLocal
import PrimeSquares.RealOrdinaryLocalOperator

namespace PrimeSquares

theorem realCombinedPhysicalKernel_local {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (active : Bool) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution (realCombinedPhysicalKernel N q₀ χ₀ Q β M active) F f x‖ ≤
      (8*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA : 0 ≤ 2*lowSpatialConstant*Q*Real.log (2*Q) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) lowSpatialConstant_nonneg) (by linarith))
      (Real.log_nonneg (by linarith))
  have hK : ∀ z : ℤ,‖realCombinedPhysicalKernel N q₀ χ₀ Q β M active z‖ ≤
      (2*lowSpatialConstant*Q*Real.log (2*Q))/(N : ℝ)^2*decayProfile ((N : ℝ)^2) 10 z := by
    intro z
    convert realCombinedPhysicalKernel_decay hN hQ q₀ χ₀ hχ hβ M active z using 1
    unfold realLowAmplitude
    ring
  have h := finiteConvolution_local_mass (realCombinedPhysicalKernel N q₀ χ₀ Q β M active)
    hA (sq_pos_of_pos hNp) hK F f x
  convert h using 1
  ring

theorem realCombinedLowModel_local {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (active : Bool)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖integerMultiplier (realCombinedLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M active) (finiteInputLp F f 2) x‖ ≤
      (8*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  have he : fourierKernel (realCombinedLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M active)=
      realCombinedPhysicalKernel N q₀ χ₀ Q β M active := funext (realCombinedLowModel_kernel _ _ _ _ _ _ _ _ _)
  rw [integerMultiplier_finite_convolution]
  change ‖finiteConvolution _ F f x‖ ≤ _
  rw [he]
  exact realCombinedPhysicalKernel_local hN hQ q₀ χ₀ hχ hβ M active F f x

end PrimeSquares
