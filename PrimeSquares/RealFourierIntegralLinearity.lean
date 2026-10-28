import PrimeSquares.ContinuousAnnularKernelFourier

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem realFourier_add {f g : ℝ→ℂ} (hf : Integrable f volume) (hg : Integrable g volume) (θ : ℝ) :
    𝓕 (fun x => f x+g x) θ=𝓕 f θ+𝓕 g θ := by
  simp only [Real.fourier_eq,smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff θ).mpr hf)
    ((Real.fourierIntegral_convergent_iff θ).mpr hg)

theorem realFourier_smul (f : ℝ→ℂ) (c : ℂ) (θ : ℝ) :
    𝓕 (fun x => c*f x) θ=c*𝓕 f θ := by
  simp only [Real.fourier_eq]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [smul_eq_mul] using smul_comm (Real.fourierChar (-inner ℝ x θ)) c (f x))

theorem realFourier_sub {f g : ℝ→ℂ} (hf : Integrable f volume) (hg : Integrable g volume) (θ : ℝ) :
    𝓕 (fun x => f x-g x) θ=𝓕 f θ-𝓕 g θ := by
  have hi : Integrable (fun x => (-1 : ℂ)*g x) volume := hg.const_mul (-1)
  have he : (fun x => f x-g x)=(fun x => f x+(-1 : ℂ)*g x) := by
    funext x
    ring
  rw [he,realFourier_add hf hi,realFourier_smul]
  ring

theorem realFourier_finsetSum {ι : Type*} (s : Finset ι) (f : ι→ℝ→ℂ)
    (hf : ∀ i∈s,Integrable (f i) volume) (θ : ℝ) :
    𝓕 (fun x => ∑ i∈s,f i x) θ=∑ i∈s,𝓕 (f i) θ := by
  simp only [Real.fourier_eq,Finset.smul_sum]
  exact integral_finsetSum s (fun i hi => (Real.fourierIntegral_convergent_iff θ).mpr (hf i hi))

end PrimeSquares
