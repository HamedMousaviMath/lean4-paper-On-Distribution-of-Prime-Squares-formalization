import PrimeSquares.RealInverseFourierIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem real_inverse_fourier_dilate (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => f (a*ξ)) x=Complex.ofReal a⁻¹*𝓕⁻ f (x/a) := by
  rw [real_inverse_fourier_integral,real_inverse_fourier_integral]
  let g : ℝ → ℂ := fun y => realFourierPhase (y*(x/a))*f y
  have he : (fun ξ : ℝ => realFourierPhase (ξ*x)*f (a*ξ))=(fun ξ : ℝ => g (a*ξ)) := by
    funext ξ
    dsimp only [g]
    congr 2
    field_simp
  rw [he,Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr ha)]
  rfl

theorem real_inverse_fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ (fun ξ => c*f ξ) x=c*𝓕⁻ f x := by
  simp only [real_inverse_fourier_integral,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

end PrimeSquares
