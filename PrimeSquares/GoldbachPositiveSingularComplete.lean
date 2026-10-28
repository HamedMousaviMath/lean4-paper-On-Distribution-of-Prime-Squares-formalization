import PrimeSquares.GoldbachSourceDensity

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff
namespace PrimeSquares

noncomputable def goldbachArchimedeanIntegral (ℓ : ℕ) (n U W : ℝ) : ℂ :=
  ∫ u in Set.Icc 2 U,Complex.ofReal ((Real.log u)⁻¹)*goldbachLogWindow W ((n-u^2)/(ℓ:ℝ))

theorem goldbach_archimedean_integral_domain (ℓ : ℕ) (n U W : ℝ) :
    goldbachArchimedeanIntegral ℓ n U W=
      ∫ u in {u : ℝ | u∈Set.Icc 2 U ∧ (n-u^2)/(ℓ:ℝ)∈Set.Icc 2 W},
        Complex.ofReal (1/(Real.log u*Real.log ((n-u^2)/(ℓ:ℝ)))) := by
  have hm : Measurable (fun u : ℝ=>(n-u^2)/(ℓ:ℝ)) := by fun_prop
  have hs : MeasurableSet {u : ℝ | u∈Set.Icc 2 U ∧ (n-u^2)/(ℓ:ℝ)∈Set.Icc 2 W} :=
    measurableSet_Icc.inter (hm measurableSet_Icc)
  unfold goldbachArchimedeanIntegral
  rw [←integral_indicator measurableSet_Icc,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with u
  simp only [goldbachLogWindow,Set.indicator_apply,Set.mem_ofPred_eq]
  by_cases hu : u∈Set.Icc (2:ℝ) U <;>
    by_cases hv : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) W <;>
    simp only [hu,hv,true_and,false_and,ite_true,ite_false,mul_zero]
  simp [one_div,mul_comm]

theorem goldbach_source_density_archimedean (N ℓ : ℕ) (hℓ : 0<ℓ)
    {n U W : ℝ} (hn : n<(N:ℝ)^2) :
    (ℓ:ℂ)*goldbachSourceDensity N ℓ U W n=goldbachArchimedeanIntegral ℓ n U W := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hc : (((ℓ:ℝ):ℂ))=(ℓ:ℂ) := by norm_cast
  have hcz : (ℓ:ℂ)≠0 := by exact_mod_cast hℓ.ne'
  unfold goldbachSourceDensity goldbachQuadraticAverage goldbachArchimedeanIntegral
  rw [hc,←mul_assoc,mul_inv_cancel₀ hcz,one_mul,
    ←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  have hc : (n-u^2)/(ℓ:ℝ)<(N:ℝ)^2/ℓ :=
    (div_lt_div_iff_of_pos_right hl).mpr (by nlinarith [hu.1])
  by_cases hv : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) W
  · have hv' : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) (min W ((N:ℝ)^2/ℓ)) :=
      ⟨hv.1,le_min hv.2 hc.le⟩
    simp only [goldbachLogWindow,Set.indicator_of_mem hv,Set.indicator_of_mem hv']
  · have hv' : (n-u^2)/(ℓ:ℝ)∉Set.Icc (2:ℝ) (min W ((N:ℝ)^2/ℓ)) := by
      intro h
      exact hv ⟨h.1,h.2.trans (min_le_left _ _)⟩
    simp only [goldbachLogWindow,Set.indicator_of_notMem hv,Set.indicator_of_notMem hv',mul_zero]

theorem goldbach_source_unsmoothed_inverse (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ)
    {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (n : ℝ) :
    goldbachUnsmoothedSingularIntegral N ℓ n U W=(ℓ:ℂ)*goldbachSourceDensity N ℓ U W n := by
  have hi := goldbach_source_density_integrable N ℓ hℓ hU hW hX
  have hf : 𝓕 (goldbachSourceDensity N ℓ U W)=
      (fun γ : ℝ=>goldbachSquareIntegral U (-γ)*goldbachLinearSourceIntegral N ℓ W (-γ)) :=
    funext (goldbach_source_density_fourier N ℓ hℓ hU hW hX)
  have hft : Integrable (𝓕 (goldbachSourceDensity N ℓ U W)) := by
    rw [hf]
    exact (goldbach_euclidean_product_integrable N ℓ hN hℓ hU hUN hW hX).1.comp_neg
  have hInv := congrFun ((goldbach_source_density_continuous N ℓ hℓ hU).fourierInv_fourier_eq hi hft) n
  have he : 𝓕⁻ (𝓕 (goldbachSourceDensity N ℓ U W)) n=
      ∫ γ : ℝ,goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ) := by
    rw [real_inverse_fourier_integral,hf]
    have hneg := integral_neg_eq_self
      (fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)) volume
    apply Eq.trans _ hneg
    apply integral_congr_ae
    filter_upwards with γ
    have hp : γ*n= -n*(-γ) := by ring
    rw [hp]
    ring
  unfold goldbachUnsmoothedSingularIntegral
  rw [←he,hInv]

theorem goldbach_unsmoothed_archimedean_complete (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ)
    {U W n : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (hn : n<(N:ℝ)^2) :
    goldbachUnsmoothedSingularIntegral N ℓ n U W=goldbachArchimedeanIntegral ℓ n U W := by
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · rw [goldbach_source_unsmoothed_inverse N ℓ hN hℓ hU hUN hW hX,
      goldbach_source_density_archimedean N ℓ hℓ hn]
  · have hJ (γ : ℝ) : goldbachLinearSourceIntegral N ℓ W γ=0 := by
      rw [goldbach_linear_source_integral N ℓ hℓ,goldbachLinearIntegral,
        Set.Ioc_eq_empty_of_le ((min_le_right _ _).trans (le_of_not_ge hX))]
      simp only [Measure.restrict_empty,integral_zero_measure]
    have hz : goldbachUnsmoothedSingularIntegral N ℓ n U W=0 := by
      simp only [goldbachUnsmoothedSingularIntegral,hJ,mul_zero,zero_mul,integral_zero]
    have hD : goldbachArchimedeanIntegral ℓ n U W=0 := by
      unfold goldbachArchimedeanIntegral
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro u hu
      have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
      have hu' : (n-u^2)/(ℓ:ℝ)<2 := by
        have hc : (n-u^2)/(ℓ:ℝ)<(N:ℝ)^2/ℓ :=
          (div_lt_div_iff_of_pos_right hl).mpr (by nlinarith [hu.1])
        exact hc.trans_le (le_of_not_ge hX)
      simp only [goldbachLogWindow,Set.indicator_of_notMem (show (n-u^2)/(ℓ:ℝ)∉Set.Icc (2:ℝ) W from fun h=>not_lt_of_ge h.1 hu'),mul_zero]
    rw [hz,hD]

theorem goldbach_smooth_compact_seed_nonzero (ψ : ℝ→ℝ) (hc : HasCompactSupport ψ)
    (hs : ContDiff ℝ ∞ ψ) (hψ : ψ≠0) : hc.toSchwartzMap hs≠0 := by
  intro he
  apply hψ
  funext x
  have h := congrArg (fun f : SchwartzMap ℝ ℝ=>f x) he
  change ψ x=0 at h
  exact h

theorem goldbach_eta_of_smooth_compact_seed (ψ : ℝ→ℝ) (hc : HasCompactSupport ψ)
    (hs : ContDiff ℝ ∞ ψ) (x : ℝ) :
    goldbachEta (hc.toSchwartzMap hs) x=
      Complex.ofReal ((∫ t : ℝ,ψ t*ψ (t-x))/(∫ t : ℝ,ψ t*ψ t)) := by
  rw [goldbachEta,smul_apply,smul_eq_mul,goldbach_autocorrelation_integral]
  change (Complex.ofReal (∫ t : ℝ,ψ t*ψ t))⁻¹*Complex.ofReal (∫ t : ℝ,ψ t*ψ (t-x))=_
  rw [←Complex.ofReal_inv,←Complex.ofReal_mul]
  congr 1
  ring

theorem goldbach_positive_singular_integral_complete (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N ℓ : ℕ,0<N →0<ℓ →∀ R U W n : ℝ,
      0<R →2≤U →U≤N →2≤W →n<(N:ℝ)^2 →
      0≤(goldbachSingularIntegral ψ N ℓ R n U W).re ∧
      (goldbachSingularIntegral ψ N ℓ R n U W).im=0 ∧
      ‖goldbachSingularIntegral ψ N ℓ R n U W-goldbachArchimedeanIntegral ℓ n U W‖≤
        K*(N:ℝ)/Real.sqrt R := by
  obtain ⟨K,hK,hbound⟩ := goldbach_singular_smoothing_uniform ψ hψ
  refine ⟨K,hK,?_⟩
  intro N ℓ hN hℓ R U W n hR hU hUN hW hn
  have hp := goldbach_singular_integral_nonnegative ψ hψ N ℓ hN hℓ hR hU hW n
  refine ⟨hp.1,hp.2,?_⟩
  rw [←goldbach_unsmoothed_archimedean_complete N ℓ hN hℓ hU hUN hW hn]
  exact hbound N ℓ hN hℓ R U W n hR hU hUN hW

end PrimeSquares
