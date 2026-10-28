import PrimeSquares.RealFourierIntegralLinearity
import PrimeSquares.ScaledCutoffInverseIdentity

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

noncomputable def cutoffL1Constant : ℝ := ∫ x : ℝ,‖sourceCutoffInverse x‖

theorem cutoffL1Constant_nonneg : 0≤cutoffL1Constant := integral_nonneg (fun _ => norm_nonneg _)

theorem scaledCutoffKernel_integrable {a : ℝ} (ha : 0<a) :
    Integrable (scaledCutoffKernel a) volume :=
  (sourceCutoffInverse.integrable.comp_div ha.ne').const_mul (Complex.ofReal a⁻¹)

theorem scaledCutoffKernel_integral_norm {a : ℝ} (ha : 0<a) :
    (∫ x,‖scaledCutoffKernel a x‖)=cutoffL1Constant := by
  have he (x : ℝ) : ‖scaledCutoffKernel a x‖=a⁻¹*‖sourceCutoffInverse (x/a)‖ := by
    rw [scaledCutoffKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr ha.le)]
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_div (fun x : ℝ => ‖sourceCutoffInverse x‖) a,abs_of_pos ha,smul_eq_mul]
  unfold cutoffL1Constant
  rw [←mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]

theorem real_fourier_dilate (f : ℝ→ℂ) {a : ℝ} (ha : 0<a) (θ : ℝ) :
    𝓕 (fun x => f (a*x)) θ=Complex.ofReal a⁻¹*𝓕 f (θ/a) := by
  have he := real_inverse_fourier_dilate f ha (-θ)
  simpa only [Real.fourierInv_eq_fourier_neg,neg_neg,neg_div] using he

theorem scaledCutoffKernel_fourier {a : ℝ} (ha : 0<a) (θ : ℝ) :
    𝓕 (scaledCutoffKernel a) θ=Complex.ofReal (sourceArcCutoff (a*θ)) := by
  unfold scaledCutoffKernel
  rw [realFourier_smul]
  have he : (fun x : ℝ => sourceCutoffInverse (x/a))=
      (fun x : ℝ => sourceCutoffInverse (a⁻¹*x)) := by
    funext x
    congr 1
    ring
  rw [he,real_fourier_dilate _ (inv_pos.mpr ha),inv_inv,
    show θ/a⁻¹=a*θ by simp only [div_eq_mul_inv,inv_inv,mul_comm],sourceCutoffInverse_fourier]
  rw [←mul_assoc,←Complex.ofReal_mul,inv_mul_cancel₀ ha.ne',Complex.ofReal_one,one_mul]

end PrimeSquares
