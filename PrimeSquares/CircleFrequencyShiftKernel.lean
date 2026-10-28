import PrimeSquares.CircleAnnularCutoffKernel
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory
namespace PrimeSquares

noncomputable def circleFrequencyShift (m : C(PrimeCircle, ℂ)) (r : PrimeCircle) : C(PrimeCircle, ℂ) :=
  m.comp ⟨fun θ => θ-r,continuous_id.sub continuous_const⟩

theorem integer_circle_character_add (x : ℤ) (θ r : PrimeCircle) :
    (fourier x (θ+r) : ℂ)=fourier x θ*fourier x r := by
  simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]

theorem circleFrequencyShift_kernel (m : C(PrimeCircle, ℂ)) (r : PrimeCircle) (x : ℤ) :
    fourierKernel (circleFrequencyShift m r) x=(fourier x r : ℂ)*fourierKernel m x := by
  simp only [fourierKernel_coefficient,fourierCoeff,neg_neg,smul_eq_mul]
  change (∫ θ : PrimeCircle,(fourier x θ : ℂ)*m (θ-r) ∂AddCircle.haarAddCircle)=_
  have h := integral_sub_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun θ : PrimeCircle => (fourier x (θ+r) : ℂ)*m θ) r
  simp only [sub_add_cancel] at h
  rw [h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [integer_circle_character_add]
  ring

theorem circleFrequencyShift_real_kernel (m : C(PrimeCircle, ℂ)) (r : ℝ) (x : ℤ) :
    fourierKernel (circleFrequencyShift m (r : PrimeCircle)) x=realFourierPhase (r*(x : ℝ))*fourierKernel m x := by
  rw [circleFrequencyShift_kernel,realFourierPhase_integer_character]

end PrimeSquares
