import PrimeSquares.GoldbachPositiveFourierAverage
import PrimeSquares.GoldbachEuclideanProduct

set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachSingularIntegral (ψ : 𝓢(ℝ,ℝ)) (N ℓ : ℕ) (R n U W : ℝ) : ℂ :=
  (ℓ:ℂ)*∫ γ : ℝ,(goldbachEta ψ ((N:ℝ)^2*γ/R))^2*
    goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)

theorem goldbach_euclidean_product_density (N ℓ : ℕ) (hℓ : 0<ℓ) (U W γ : ℝ) :
    goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ=
      ∫ z : ℝ×ℝ,realFourierPhase (γ*(z.1^2+(ℓ:ℝ)*z.2))*
        (((Real.log z.1)⁻¹*(Real.log z.2)⁻¹:ℝ):ℂ)
        ∂((volume.restrict (Set.Ioc 2 U)).prod
          (volume.restrict (Set.Ioc 2 (min W ((N:ℝ)^2/ℓ))))) := by
  rw [goldbach_linear_source_integral N ℓ hℓ]
  unfold goldbachSquareIntegral goldbachLinearIntegral
  rw [←integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [realFourierPhase_quadratic,neg_neg]
  have he : γ*(z.1^2+(ℓ:ℝ)*z.2)=γ*z.1^2+((ℓ:ℝ)*γ)*z.2 := by ring
  rw [he,realFourierPhase_add]
  push_cast
  ring

theorem goldbach_singular_integral_positive (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ) {R U W : ℝ} (hR : 0<R)
    (hU : 2≤U) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (n : ℝ) :
    0≤(goldbachSingularIntegral ψ N ℓ R n U W).re ∧
      (goldbachSingularIntegral ψ N ℓ R n U W).im=0 := by
  let T := min W ((N:ℝ)^2/ℓ)
  have hT : 2≤T := le_min hW hX
  let ν := (volume.restrict (Set.Ioc 2 U)).prod (volume.restrict (Set.Ioc 2 T))
  let w := fun z : ℝ×ℝ=>(Real.log z.1)⁻¹*(Real.log z.2)⁻¹
  let ξ := fun z : ℝ×ℝ=>z.1^2+(ℓ:ℝ)*z.2
  have hw : Measurable w :=
    (Real.measurable_log.comp measurable_fst).inv.mul (Real.measurable_log.comp measurable_snd).inv
  have hξ : Measurable ξ := by fun_prop
  have hiU : IntegrableOn (fun t : ℝ=>(Real.log t)⁻¹) (Set.Ioc 2 U) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mp
      (goldbach_log_density_continuousOn.mono (by
        rw [Set.uIcc_of_le hU]
        exact Set.Icc_subset_Ici_self)).intervalIntegrable
  have hiT : IntegrableOn (fun t : ℝ=>(Real.log t)⁻¹) (Set.Ioc 2 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      (goldbach_log_density_continuousOn.mono (by
        rw [Set.uIcc_of_le hT]
        exact Set.Icc_subset_Ici_self)).intervalIntegrable
  have hwi : Integrable w ν := hiU.mul_prod hiT
  have hw0 : ∀ᵐ z ∂ν,0≤w z := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    exact mul_nonneg (inv_nonneg.mpr (Real.log_pos (by linarith [hz.1.1])).le)
      (inv_nonneg.mpr (Real.log_pos (by linarith [hz.2.1])).le)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hρ : 0<(N:ℝ)^2/R := by positivity
  let κ := goldbachCutoffSquare (goldbachScaleSchwartz (goldbachEta ψ) ((N:ℝ)^2/R) hρ.ne')
  have hκ : ∀ x : ℝ,0≤(𝓕⁻ (κ:ℝ→ℂ) x).re ∧ (𝓕⁻ (κ:ℝ→ℂ) x).im=0 :=
    goldbach_cutoff_square_inverse_nonnegative _ (goldbach_scaled_eta_inverse_nonnegative ψ hψ hρ)
  have hp := goldbach_positive_cutoff_fourier_average κ hκ ν w ξ hw hwi hw0 hξ n
  have he : goldbachSingularIntegral ψ N ℓ R n U W=
      (ℓ:ℂ)*(∫ γ : ℝ,κ γ*(∫ z : ℝ×ℝ,realFourierPhase (γ*ξ z)*(w z:ℂ) ∂ν)*realFourierPhase (-n*γ)) := by
    unfold goldbachSingularIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards with γ
    have hκγ : κ γ=(goldbachEta ψ ((N:ℝ)^2*γ/R))^2 := by
      simp only [κ,goldbachCutoffSquare_apply,goldbachScaleSchwartz_apply,pow_two]
      congr 2 <;> ring
    rw [hκγ,←goldbach_euclidean_product_density N ℓ hℓ]
    ring
  rw [he,Complex.mul_re,Complex.mul_im]
  simp only [Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,zero_add,hp.2,mul_zero]
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hp.1,trivial⟩

theorem goldbach_singular_integral_empty (ψ : 𝓢(ℝ,ℝ)) (N ℓ : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hX : (N:ℝ)^2/ℓ≤2) (R n U : ℝ) :
    goldbachSingularIntegral ψ N ℓ R n U W=0 := by
  have he (γ : ℝ) : goldbachLinearSourceIntegral N ℓ W γ=0 := by
    rw [goldbach_linear_source_integral N ℓ hℓ,goldbachLinearIntegral,
      Set.Ioc_eq_empty_of_le ((min_le_right _ _).trans hX)]
    simp only [Measure.restrict_empty,integral_zero_measure]
  simp only [goldbachSingularIntegral,he,mul_zero,zero_mul,integral_zero]

theorem goldbach_singular_integral_nonnegative (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ) {R U W : ℝ} (hR : 0<R)
    (hU : 2≤U) (hW : 2≤W) (n : ℝ) :
    0≤(goldbachSingularIntegral ψ N ℓ R n U W).re ∧
      (goldbachSingularIntegral ψ N ℓ R n U W).im=0 := by
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · exact goldbach_singular_integral_positive ψ hψ N ℓ hN hℓ hR hU hW hX n
  · rw [goldbach_singular_integral_empty ψ N ℓ hℓ (le_of_not_ge hX)]
    exact ⟨le_rfl,rfl⟩

end PrimeSquares
