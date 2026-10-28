import PrimeSquares.GoldbachIntegrableDecay
import PrimeSquares.RealInverseFourierIntegral

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_cutoff_fourier_fubini (κ : 𝓢(ℝ,ℂ)) (ν : Measure (ℝ×ℝ)) [SFinite ν]
    (w ξ : (ℝ×ℝ)→ℝ) (hw : Measurable w) (hwi : Integrable w ν) (hξ : Measurable ξ) (n : ℝ) :
    (∫ γ : ℝ,κ γ*(∫ z : ℝ×ℝ,realFourierPhase (γ*ξ z)*(w z:ℂ) ∂ν)*realFourierPhase (-n*γ))=
      ∫ z : ℝ×ℝ,(w z:ℂ)*𝓕⁻ (κ:ℝ→ℂ) (ξ z-n) ∂ν := by
  let F := fun p : ℝ×(ℝ×ℝ)=>κ p.1*realFourierPhase (p.1*(ξ p.2-n))*(w p.2:ℂ)
  have hsm : StronglyMeasurable F := by
    exact (((κ.continuous.measurable.comp measurable_fst).mul
      (realFourierPhase_continuous.measurable.comp
        (measurable_fst.mul ((hξ.comp measurable_snd).sub_const n)))).mul
      (Complex.continuous_ofReal.measurable.comp (hw.comp measurable_snd))).stronglyMeasurable
  have hi : Integrable F (volume.prod ν) :=
    ((κ.integrable (μ:=volume)).norm.mul_prod hwi.norm).mono' hsm.aestronglyMeasurable (by
      filter_upwards with p
      simp only [F,norm_mul,realFourierPhase_norm,mul_one,Complex.norm_real]
      exact le_rfl)
  have he (γ : ℝ) : κ γ*(∫ z : ℝ×ℝ,realFourierPhase (γ*ξ z)*(w z:ℂ) ∂ν)*realFourierPhase (-n*γ)=
      ∫ z : ℝ×ℝ,F (γ,z) ∂ν := by
    rw [←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with z
    have hph : realFourierPhase (γ*ξ z)*realFourierPhase (-n*γ)=realFourierPhase (γ*(ξ z-n)) := by
      rw [←realFourierPhase_add]
      congr 1
      ring
    dsimp only [F]
    calc
      _=κ γ*(realFourierPhase (γ*ξ z)*realFourierPhase (-n*γ))*(w z:ℂ) := by ring
      _=_ := by rw [hph]
  calc
    _=∫ γ : ℝ,∫ z : ℝ×ℝ,F (γ,z) ∂ν := by simp only [he]
    _=∫ z : ℝ×ℝ,(∫ γ : ℝ,F (γ,z)) ∂ν := integral_integral_swap hi
    _=_ := by
      apply integral_congr_ae
      filter_upwards with z
      change (∫ γ : ℝ,κ γ*realFourierPhase (γ*(ξ z-n))*(w z:ℂ))=_
      rw [integral_mul_const,real_inverse_fourier_integral]
      rw [mul_comm (∫ γ : ℝ,κ γ*realFourierPhase (γ*(ξ z-n)))]
      congr 1
      apply integral_congr_ae
      filter_upwards with γ
      ring

theorem goldbach_positive_cutoff_fourier_average (κ : 𝓢(ℝ,ℂ))
    (hκ : ∀ x : ℝ,0≤(𝓕⁻ (κ:ℝ→ℂ) x).re ∧ (𝓕⁻ (κ:ℝ→ℂ) x).im=0)
    (ν : Measure (ℝ×ℝ)) [SFinite ν] (w ξ : (ℝ×ℝ)→ℝ)
    (hw : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ᵐ z ∂ν,0≤w z)
    (hξ : Measurable ξ) (n : ℝ) :
    0≤(∫ γ : ℝ,κ γ*(∫ z : ℝ×ℝ,realFourierPhase (γ*ξ z)*(w z:ℂ) ∂ν)*realFourierPhase (-n*γ)).re ∧
      (∫ γ : ℝ,κ γ*(∫ z : ℝ×ℝ,realFourierPhase (γ*ξ z)*(w z:ℂ) ∂ν)*realFourierPhase (-n*γ)).im=0 := by
  rw [goldbach_cutoff_fourier_fubini κ ν w ξ hw hwi hξ n]
  have he : (fun z : ℝ×ℝ=>(w z:ℂ)*𝓕⁻ (κ:ℝ→ℂ) (ξ z-n))=
      (fun z=>Complex.ofReal (w z*(𝓕⁻ (κ:ℝ→ℂ) (ξ z-n)).re)) := by
    funext z
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,(hκ (ξ z-n)).2,mul_zero,zero_mul,sub_zero,add_zero]
  rw [he]
  have hi : (∫ z : ℝ×ℝ,Complex.ofReal (w z*(𝓕⁻ (κ:ℝ→ℂ) (ξ z-n)).re) ∂ν)=
      Complex.ofReal (∫ z : ℝ×ℝ,w z*(𝓕⁻ (κ:ℝ→ℂ) (ξ z-n)).re ∂ν) := integral_ofReal
  rw [hi]
  refine ⟨integral_nonneg_of_ae ?_,rfl⟩
  filter_upwards [hw0] with z hz
  exact mul_nonneg hz (hκ (ξ z-n)).1

end PrimeSquares
