import PrimeSquares.RealFourierPhase
import PrimeSquares.CircleFourier

open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem real_inverse_fourier_integral (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ f x=∫ ξ : ℝ,realFourierPhase (ξ*x)*f ξ := by
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [show -2*Real.pi*ξ*(-x)=2*Real.pi*(ξ*x) by ring]
  rfl

theorem realFourierPhase_integer_character (x : ℤ) (ξ : ℝ) :
    (fourier x (ξ : PrimeCircle) : ℂ)=realFourierPhase (ξ*(x : ℝ)) := by
  calc
    (fourier x (ξ : PrimeCircle) : ℂ)=negativeFourierCharacter (-x) (ξ : PrimeCircle) := by
      simp only [negativeFourierCharacter,neg_neg]
    _ = _ := negativeFourierCharacter_real (-x) ξ
    _ = realFourierPhase (ξ*(x : ℝ)) := by
      unfold realFourierPhase
      congr 1
      push_cast
      ring

theorem realFourierPhase_integer (n : ℤ) : realFourierPhase (n : ℝ)=1 := by
  unfold realFourierPhase
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  congr 1
  push_cast
  ring

end PrimeSquares
