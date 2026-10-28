import PrimeSquares.GoldbachArithmeticComplete
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap Convolution
namespace PrimeSquares

noncomputable def goldbachComplexSeed (ψ : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM ψ

noncomputable def goldbachReflectedSeed (ψ : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) (goldbachComplexSeed ψ)

noncomputable def goldbachAutocorrelation (ψ : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (goldbachComplexSeed ψ) (goldbachReflectedSeed ψ)

noncomputable def goldbachSeedMass (ψ : 𝓢(ℝ,ℝ)) : ℝ := ∫ t : ℝ,ψ t*ψ t

@[simp] theorem goldbachComplexSeed_apply (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    goldbachComplexSeed ψ x=(ψ x:ℂ) := rfl

@[simp] theorem goldbachReflectedSeed_apply (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    goldbachReflectedSeed ψ x=(ψ (-x):ℂ) := rfl

theorem goldbach_autocorrelation_integral (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    goldbachAutocorrelation ψ x=((∫ t : ℝ,ψ t*ψ (t-x)):ℝ) := by
  rw [goldbachAutocorrelation,SchwartzMap.convolution_apply]
  simp only [convolution,ContinuousLinearMap.mul_apply',goldbachComplexSeed_apply,
    goldbachReflectedSeed_apply,neg_sub,←Complex.ofReal_mul]
  exact integral_ofReal

theorem goldbach_seed_mass_pos (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) : 0<goldbachSeedMass ψ := by
  have hi : Integrable (fun t : ℝ=>ψ t*ψ t) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) ψ ψ).integrable
  have hn : 0≤goldbachSeedMass ψ := integral_nonneg (fun t=>mul_self_nonneg (ψ t))
  apply lt_of_le_of_ne hn
  intro hz
  have hae : (fun t : ℝ=>ψ t*ψ t)=ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t=>mul_self_nonneg (ψ t)) hi).mp hz.symm
  have he : (fun t : ℝ=>ψ t*ψ t)=0 :=
    ((ψ.continuous.mul ψ.continuous).ae_eq_iff_eq volume continuous_const).mp hae
  apply hψ
  ext t
  have ht := congrFun he t
  simpa only [Pi.zero_apply,mul_self_eq_zero,zero_apply] using ht

theorem goldbach_autocorrelation_zero (ψ : 𝓢(ℝ,ℝ)) :
    goldbachAutocorrelation ψ 0=(goldbachSeedMass ψ:ℂ) := by
  simp only [goldbach_autocorrelation_integral,sub_zero,goldbachSeedMass]

theorem goldbach_real_seed_fourier_conj (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    𝓕 (goldbachComplexSeed ψ : ℝ→ℂ) (-x)=
      starRingEnd ℂ (𝓕 (goldbachComplexSeed ψ : ℝ→ℂ) x) := by
  rw [Real.fourier_eq,Real.fourier_eq,←integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  change ((𝐞 (-inner ℝ t (-x))):ℂ)*(ψ t:ℂ)=
    starRingEnd ℂ (((𝐞 (-inner ℝ t x)):ℂ)*(ψ t:ℂ))
  rw [map_mul,Complex.conj_ofReal,←Circle.coe_inv_eq_conj,←AddChar.map_neg_eq_inv]
  simp only [inner_neg_right,neg_neg]


theorem goldbach_reflected_seed_fourier (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    𝓕 (goldbachReflectedSeed ψ : ℝ→ℂ) x=
      starRingEnd ℂ (𝓕 (goldbachComplexSeed ψ : ℝ→ℂ) x) := by
  change 𝓕 ((goldbachComplexSeed ψ : ℝ→ℂ) ∘ LinearIsometryEquiv.neg ℝ) x=_
  rw [Real.fourier_comp_linearIsometry]
  exact goldbach_real_seed_fourier_conj ψ x

theorem goldbach_autocorrelation_fourier (ψ : 𝓢(ℝ,ℝ)) (x : ℝ) :
    𝓕 (goldbachAutocorrelation ψ : ℝ→ℂ) x=
      (Complex.normSq (𝓕 (goldbachComplexSeed ψ : ℝ→ℂ) x):ℂ) := by
  have he : (goldbachAutocorrelation ψ : ℝ→ℂ)=
      (goldbachComplexSeed ψ : ℝ→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (goldbachReflectedSeed ψ : ℝ→ℂ) := by
    funext t
    exact SchwartzMap.convolution_apply _ _ _ t
  rw [he,Real.fourier_mul_convolution_eq (goldbachComplexSeed ψ).integrable
    (goldbachReflectedSeed ψ).integrable,goldbach_reflected_seed_fourier,Complex.mul_conj]

noncomputable def goldbachEta (ψ : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  (goldbachSeedMass ψ:ℂ)⁻¹ • goldbachAutocorrelation ψ

theorem goldbach_eta_zero (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) : goldbachEta ψ 0=1 := by
  simp only [goldbachEta,smul_apply,smul_eq_mul,goldbach_autocorrelation_zero]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (goldbach_seed_mass_pos ψ hψ).ne')

theorem goldbach_eta_inverse_fourier_nonnegative (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) (x : ℝ) :
    0≤(𝓕⁻ (goldbachEta ψ : ℝ→ℂ) x).re ∧ (𝓕⁻ (goldbachEta ψ : ℝ→ℂ) x).im=0 := by
  have hf : 𝓕 (goldbachEta ψ : ℝ→ℂ) (-x)=
      (goldbachSeedMass ψ:ℂ)⁻¹*𝓕 (goldbachAutocorrelation ψ : ℝ→ℂ) (-x) := by
    rw [Real.fourier_eq,Real.fourier_eq,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    change ((𝐞 (-inner ℝ t (-x))):ℂ)*((goldbachSeedMass ψ:ℂ)⁻¹*goldbachAutocorrelation ψ t)=_
    change _=(goldbachSeedMass ψ:ℂ)⁻¹*(((𝐞 (-inner ℝ t (-x))):ℂ)*goldbachAutocorrelation ψ t)
    ring
  rw [Real.fourierInv_eq_fourier_neg,hf,goldbach_autocorrelation_fourier,
    ←Complex.ofReal_inv,←Complex.ofReal_mul]
  simp only [Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨mul_nonneg (inv_nonneg.mpr (goldbach_seed_mass_pos ψ hψ).le) (Complex.normSq_nonneg _),trivial⟩

end PrimeSquares
