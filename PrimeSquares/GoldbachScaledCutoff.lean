import PrimeSquares.GoldbachAutocorrelation

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap Convolution
namespace PrimeSquares

noncomputable def goldbachScaleSchwartz (f : 𝓢(ℝ,ℂ)) (ρ : ℝ) (hρ : ρ≠0) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 ρ hρ)) f

@[simp] theorem goldbachScaleSchwartz_apply (f : 𝓢(ℝ,ℂ)) (ρ : ℝ) (hρ : ρ≠0) (x : ℝ) :
    goldbachScaleSchwartz f ρ hρ x=f (x*ρ) := rfl

theorem goldbach_inverse_fourier_scale (f : ℝ→ℂ) {ρ : ℝ} (hρ : 0<ρ) (x : ℝ) :
    𝓕⁻ (fun t=>f (t*ρ)) x=ρ⁻¹ • 𝓕⁻ f (x/ρ) := by
  rw [Real.fourierInv_eq,Real.fourierInv_eq]
  have hi := Measure.integral_comp_mul_right (fun t : ℝ=>𝐞 (inner ℝ t (x/ρ)) • f t) ρ
  simp only [abs_of_pos (inv_pos.mpr hρ)] at hi
  convert hi using 1
  congr 1
  funext t
  congr 2
  simp only [RCLike.inner_apply,conj_trivial]
  field_simp

theorem goldbach_scaled_eta_inverse_nonnegative (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    {ρ : ℝ} (hρ : 0<ρ) (x : ℝ) :
    0≤(𝓕⁻ (goldbachScaleSchwartz (goldbachEta ψ) ρ hρ.ne' : ℝ→ℂ) x).re ∧
      (𝓕⁻ (goldbachScaleSchwartz (goldbachEta ψ) ρ hρ.ne' : ℝ→ℂ) x).im=0 := by
  change 0≤(𝓕⁻ (fun t=>(goldbachEta ψ) (t*ρ)) x).re ∧
    (𝓕⁻ (fun t=>(goldbachEta ψ) (t*ρ)) x).im=0
  rw [goldbach_inverse_fourier_scale _ hρ,Complex.real_smul,Complex.mul_re,Complex.mul_im]
  have h := goldbach_eta_inverse_fourier_nonnegative ψ hψ (x/ρ)
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_add,h.2,mul_zero]
  exact ⟨mul_nonneg (inv_nonneg.mpr hρ.le) h.1,trivial⟩

noncomputable def goldbachCutoffSquare (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f f

@[simp] theorem goldbachCutoffSquare_apply (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    goldbachCutoffSquare f x=f x*f x := rfl

theorem goldbach_cutoff_square_inverse_nonnegative (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x : ℝ,0≤(𝓕⁻ (f:ℝ→ℂ) x).re ∧ (𝓕⁻ (f:ℝ→ℂ) x).im=0) (x : ℝ) :
    0≤(𝓕⁻ (goldbachCutoffSquare f : ℝ→ℂ) x).re ∧
      (𝓕⁻ (goldbachCutoffSquare f : ℝ→ℂ) x).im=0 := by
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ f
  let c : 𝓢(ℝ,ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g g
  have he : 𝓕 c=goldbachCutoffSquare f := by
    simp only [c,g,SchwartzMap.fourier_convolution,fourier_fourierInv_eq,goldbachCutoffSquare]
  have hei : (𝓕⁻ (goldbachCutoffSquare f) : 𝓢(ℝ,ℂ))=c := by rw [←he];simp
  rw [←SchwartzMap.fourierInv_coe,hei]
  have hp (t : ℝ) : g t*g (x-t)=
      (((𝓕⁻ (f:ℝ→ℂ) t).re*(𝓕⁻ (f:ℝ→ℂ) (x-t)).re:ℝ):ℂ) := by
    have hgt : g t=𝓕⁻ (f:ℝ→ℂ) t := by
      change (𝓕⁻ f : 𝓢(ℝ,ℂ)) _=_
      rw [SchwartzMap.fourierInv_coe]
    have hgs : g (x-t)=𝓕⁻ (f:ℝ→ℂ) (x-t) := by
      change (𝓕⁻ f : 𝓢(ℝ,ℂ)) _=_
      rw [SchwartzMap.fourierInv_coe]
    rw [hgt,hgs]
    apply Complex.ext <;> simp [(hf t).2,(hf (x-t)).2]
  change 0≤(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g g x).re ∧
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g g x).im=0
  rw [SchwartzMap.convolution_apply]
  simp only [convolution,ContinuousLinearMap.mul_apply',hp]
  have hi : (∫ t : ℝ,(((𝓕⁻ (f:ℝ→ℂ) t).re*(𝓕⁻ (f:ℝ→ℂ) (x-t)).re:ℝ):ℂ))=
      Complex.ofReal (∫ t : ℝ,(𝓕⁻ (f:ℝ→ℂ) t).re*(𝓕⁻ (f:ℝ→ℂ) (x-t)).re) := integral_ofReal
  rw [hi]
  exact ⟨integral_nonneg (fun t=>mul_nonneg (hf t).1 (hf (x-t)).1),rfl⟩

theorem goldbach_eta_support (ψ : 𝓢(ℝ,ℝ))
    (hs : ∀ t : ℝ,(1/8:ℝ)≤|t| →ψ t=0) {x : ℝ} (hx : (1/4:ℝ)≤|x|) :
    goldbachEta ψ x=0 := by
  have hc : goldbachAutocorrelation ψ x=0 := by
    rw [goldbach_autocorrelation_integral]
    have hz (t : ℝ) : ψ t*ψ (t-x)=0 := by
      by_cases ht : (1/8:ℝ)≤|t|
      · rw [hs t ht,zero_mul]
      · have ht' : (1/8:ℝ)≤|t-x| := by
          have hh : |x|≤|t|+|t-x| := by
            calc
              |x|=|t-(t-x)| := by congr 1;ring
              _≤|t|+|t-x| := abs_sub _ _
          linarith
        rw [hs (t-x) ht',mul_zero]
    simp only [hz,integral_zero,Complex.ofReal_zero]
  simp only [goldbachEta,smul_apply,smul_eq_mul,hc,mul_zero]

theorem goldbach_scaled_eta_support (ψ : 𝓢(ℝ,ℝ))
    (hs : ∀ t : ℝ,(1/8:ℝ)≤|t| →ψ t=0) {ρ : ℝ} (hρ : 0<ρ)
    {x : ℝ} (hx : (1/(4*ρ):ℝ)≤|x|) :
    goldbachScaleSchwartz (goldbachEta ψ) ρ hρ.ne' x=0 := by
  rw [goldbachScaleSchwartz_apply]
  apply goldbach_eta_support ψ hs
  rw [abs_mul,abs_of_pos hρ]
  have hh := mul_le_mul_of_nonneg_right hx hρ.le
  have he : (1/(4*ρ):ℝ)*ρ=1/4 := by field_simp
  linarith

end PrimeSquares
