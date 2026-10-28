import PrimeSquares.ClosedFundamentalCutoff
import PrimeSquares.NarrowFourierIntegral
import PrimeSquares.FourierKernels

open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem compactCircleLift_inverse_kernel (f : C(ℝ, ℂ))
    (hs : ∀ ξ : ℝ,1 ≤ |ξ| → f ξ=0) (hn : ∀ ξ : ℝ,1/2 ≤ |ξ| → f ξ=0) (x : ℤ) :
    fourierKernel (compactCircleLift f hs) x=𝓕⁻ (f : ℝ → ℂ) (x : ℝ) := by
  rw [fourierKernel_coefficient,fourierCoeff_eq_intervalIntegral _ (-x) (-(1/2) : ℝ)]
  norm_num only [neg_neg,div_one,one_div,one_smul]
  rw [narrow_inverse_fourier_interval f hn]
  apply intervalIntegral.integral_congr
  intro ξ hξ
  rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)] at hξ
  dsimp only
  rw [compactCircleLift_small_support_closed f hs hn hξ,realFourierPhase_integer_character]
  rfl

end PrimeSquares
