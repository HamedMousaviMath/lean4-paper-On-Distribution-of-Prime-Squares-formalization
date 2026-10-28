import PrimeSquares.GoldbachSmoothingDecay

set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachUnsmoothedSingularIntegral (N ℓ : ℕ) (n U W : ℝ) : ℂ :=
  (ℓ:ℂ)*∫ γ : ℝ,goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)

theorem goldbach_singular_smoothing_uniform (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N ℓ : ℕ,0<N →0<ℓ →∀ R U W n : ℝ,
      0<R →2≤U →U≤N →2≤W →
      ‖goldbachSingularIntegral ψ N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W‖≤
        K*(N:ℝ)/Real.sqrt R := by
  obtain ⟨K,hK,hcut⟩ := goldbach_eta_square_cutoff_bound ψ hψ
  refine ⟨6*K*goldbachEuclideanDecayConstant,by have := goldbachEuclideanDecayConstant_pos;positivity,?_⟩
  intro N ℓ hN hℓ R U W n hR hU hUN hW
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · let c := R/(N:ℝ)^2
    have hc : 0<c := by dsimp [c];positivity
    let w := fun γ : ℝ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2-1
    let f := fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)
    have hw : StronglyMeasurable w :=
      ((((goldbachEta ψ).continuous.comp (by fun_prop)).pow 2).sub continuous_const).stronglyMeasurable
    have hf : StronglyMeasurable f :=
      ((goldbachSquareIntegral_stronglyMeasurable U).mul
        (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W)).mul
        (realFourierPhase_continuous.comp (by fun_prop)).stronglyMeasurable
    have hweight (γ : ℝ) : ‖w γ‖≤K*min 1 ((|γ|/c)^2) := by
      have he : (N:ℝ)^2*γ/R=γ/c := by dsimp [c];field_simp
      dsimp only [w]
      rw [he,norm_sub_rev,pow_two]
      simpa only [abs_div,abs_of_pos hc] using hcut (γ/c)
    have hdecay (γ : ℝ) (hγ : γ≠0) : ‖f γ‖≤
        (goldbachEuclideanDecayConstant/(ℓ:ℝ))/(Real.sqrt |γ| * |γ|) := by
      have hb := goldbach_euclidean_product_decay N ℓ hℓ hU hW hX hγ
      rw [←goldbach_inverse_sqrt_power (abs_pos.mpr hγ)] at hb
      simpa only [f,norm_mul,realFourierPhase_norm,mul_one,div_eq_mul_inv] using hb
    have hi := goldbach_smoothing_decay_integrable w f hw hf hc hK.le
      (div_nonneg goldbachEuclideanDecayConstant_pos.le hl.le) hweight hdecay
    have hIJ := (goldbach_euclidean_product_integrable N ℓ hN hℓ hU hUN hW hX).1
    have hfi : Integrable f := hIJ.norm.mono' hf.aestronglyMeasurable (by
      filter_upwards with γ
      simp only [f,norm_mul,realFourierPhase_norm,mul_one]
      exact le_rfl)
    have hsi := goldbach_singular_integrand_integrable ψ hψ N ℓ hN hℓ hU hUN hW hX R n
    have he : goldbachSingularIntegral ψ N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W=
        (ℓ:ℂ)*(∫ γ : ℝ,w γ*f γ) := by
      unfold goldbachSingularIntegral goldbachUnsmoothedSingularIntegral
      rw [←mul_sub,←integral_sub hsi hfi]
      congr 1
      apply integral_congr_ae
      filter_upwards with γ
      dsimp only [w,f]
      ring
    have hs : Real.sqrt c=Real.sqrt R/(N:ℝ) := by
      dsimp only [c]
      rw [Real.sqrt_div hR.le,Real.sqrt_sq_eq_abs,abs_of_pos hn]
    rw [he,norm_mul,Complex.norm_natCast]
    calc
      _≤(ℓ:ℝ)*(∫ γ : ℝ,‖w γ*f γ‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hl.le
      _≤(ℓ:ℝ)*(6*K*(goldbachEuclideanDecayConstant/(ℓ:ℝ))/Real.sqrt c) :=
        mul_le_mul_of_nonneg_left hi.2 hl.le
      _=_ := by rw [hs];field_simp
  · have hcap : (N:ℝ)^2/ℓ≤2 := le_of_not_ge hX
    have hz : goldbachUnsmoothedSingularIntegral N ℓ n U W=0 := by
      have he (γ : ℝ) : goldbachLinearSourceIntegral N ℓ W γ=0 := by
        rw [goldbach_linear_source_integral N ℓ hℓ,goldbachLinearIntegral,
          Set.Ioc_eq_empty_of_le ((min_le_right _ _).trans hcap)]
        simp only [Measure.restrict_empty,integral_zero_measure]
      simp only [goldbachUnsmoothedSingularIntegral,he,mul_zero,zero_mul,integral_zero]
    rw [goldbach_singular_integral_empty ψ N ℓ hℓ hcap,hz,sub_self,norm_zero]
    have := goldbachEuclideanDecayConstant_pos
    positivity

end PrimeSquares
