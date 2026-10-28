import PrimeSquares.GoldbachQuadraticDensity

set_option autoImplicit false
open MeasureTheory FourierTransform
namespace PrimeSquares

noncomputable def goldbachLogWindow (T x : ℝ) : ℂ :=
  (Set.Icc 2 T).indicator (fun v : ℝ=>((Real.log v)⁻¹:ℝ)) x

theorem goldbach_log_window_measurable (T : ℝ) : Measurable (goldbachLogWindow T) :=
  (Complex.continuous_ofReal.measurable.comp Real.measurable_log.inv).indicator measurableSet_Icc

theorem goldbach_log_window_integrable {T : ℝ} (hT : 2≤T) : Integrable (goldbachLogWindow T) := by
  have hi : IntegrableOn (fun t : ℝ=>(Real.log t)⁻¹) (Set.Icc 2 T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      (goldbach_log_density_continuousOn.mono (by rw [Set.uIcc_of_le hT];exact Set.Icc_subset_Ici_self)).intervalIntegrable
  exact (integrable_indicator_iff measurableSet_Icc).mpr hi.ofReal

theorem goldbach_log_window_norm (T x : ℝ) : ‖goldbachLogWindow T x‖≤1/Real.log 2 := by
  by_cases hx : x∈Set.Icc (2:ℝ) T
  · have hl : 0<Real.log x := Real.log_pos (by linarith [hx.1])
    simp only [goldbachLogWindow,Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hl)]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.log_pos (by norm_num : (1:ℝ)<2))
      (Real.log_le_log (by norm_num : (0:ℝ)<2) hx.1)
  · simp only [goldbachLogWindow,Set.indicator_of_notMem hx,norm_zero]
    positivity

theorem goldbach_log_window_continuousAt (T : ℝ) {x : ℝ} (hx2 : x≠2) (hxT : x≠T) :
    ContinuousAt (goldbachLogWindow T) x := by
  by_cases h2 : x<2
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds h2] with y hy
    exact Set.indicator_of_notMem (by intro h;linarith [h.1,show y<2 from hy]) _
  · have h2' : 2<x := lt_of_le_of_ne (le_of_not_gt h2) hx2.symm
    by_cases hT : x<T
    · have hc : ContinuousAt (fun v : ℝ=>(((Real.log v)⁻¹:ℝ):ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuousAt_log (by linarith : x≠0)).inv₀ (Real.log_pos (by linarith : 1<x)).ne')
      apply hc.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds h2',isOpen_Iio.mem_nhds hT] with y hy2 hyT
      exact Set.indicator_of_mem (show y∈Set.Icc (2:ℝ) T from ⟨hy2.le,hyT.le⟩) _
    · have hT' : T<x := lt_of_le_of_ne (le_of_not_gt hT) hxT.symm
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hT'] with y hy
      exact Set.indicator_of_notMem (by intro h;linarith [h.2,show T<y from hy]) _

theorem goldbach_log_window_oscillatory (T β : ℝ) :
    (∫ v : ℝ,realFourierPhase (β*v)*goldbachLogWindow T v)=goldbachLinearIntegral T β := by
  have he : (fun v : ℝ=>realFourierPhase (β*v)*goldbachLogWindow T v)=
      (Set.Icc 2 T).indicator (fun v : ℝ=>realFourierPhase (β*v)*((Real.log v)⁻¹:ℝ)) := by
    funext v
    by_cases hv : v∈Set.Icc (2:ℝ) T <;> simp [goldbachLogWindow,hv]
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  rfl

noncomputable def goldbachSourceDensity (N ℓ : ℕ) (U W x : ℝ) : ℂ :=
  goldbachQuadraticAverage (volume.restrict (Set.Ioc 2 U))
    (fun u : ℝ=>Complex.ofReal ((Real.log u)⁻¹))
    (goldbachLogWindow (min W ((N:ℝ)^2/ℓ))) (ℓ:ℝ) x

theorem goldbach_source_density_integrable (N ℓ : ℕ) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) :
    Integrable (goldbachSourceDensity N ℓ U W) := by
  have hfi : IntegrableOn (fun u : ℝ=>((Real.log u)⁻¹:ℝ)) (Set.Ioc 2 U) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mp
      (goldbach_log_density_continuousOn.mono (by rw [Set.uIcc_of_le hU];exact Set.Icc_subset_Ici_self)).intervalIntegrable
  exact goldbach_quadratic_average_integrable _ _ _
    (Complex.continuous_ofReal.measurable.comp Real.measurable_log.inv)
    (goldbach_log_window_measurable _) hfi.ofReal (goldbach_log_window_integrable (le_min hW hX))
    (by exact_mod_cast hℓ)

theorem goldbach_source_density_fourier (N ℓ : ℕ) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (γ : ℝ) :
    𝓕 (goldbachSourceDensity N ℓ U W) γ=
      goldbachSquareIntegral U (-γ)*goldbachLinearSourceIntegral N ℓ W (-γ) := by
  have hfi : IntegrableOn (fun u : ℝ=>(Real.log u)⁻¹) (Set.Ioc 2 U) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mp
      (goldbach_log_density_continuousOn.mono (by rw [Set.uIcc_of_le hU];exact Set.Icc_subset_Ici_self)).intervalIntegrable
  change 𝓕 (goldbachQuadraticAverage (volume.restrict (Set.Ioc 2 U))
    (fun u : ℝ=>Complex.ofReal ((Real.log u)⁻¹))
    (goldbachLogWindow (min W ((N:ℝ)^2/ℓ))) (ℓ:ℝ)) γ=_
  rw [goldbach_quadratic_average_fourier (volume.restrict (Set.Ioc 2 U))
    (fun u : ℝ=>Complex.ofReal ((Real.log u)⁻¹)) (goldbachLogWindow (min W ((N:ℝ)^2/ℓ)))
    (Complex.continuous_ofReal.measurable.comp Real.measurable_log.inv)
    (goldbach_log_window_measurable _) hfi.ofReal (goldbach_log_window_integrable (le_min hW hX))
    (by exact_mod_cast hℓ),goldbach_log_window_oscillatory,goldbach_linear_source_integral N ℓ hℓ]
  congr 1
  · unfold goldbachSquareIntegral
    simp only [realFourierPhase_quadratic,neg_neg]
  · congr 1
    ring

theorem goldbach_source_density_continuous (N ℓ : ℕ) (hℓ : 0<ℓ) {U W : ℝ} (hU : 2≤U) :
    Continuous (goldbachSourceDensity N ℓ U W) := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  let T := min W ((N:ℝ)^2/ℓ)
  let μ := volume.restrict (Set.Ioc 2 U)
  let f := fun u : ℝ=>(((Real.log u)⁻¹:ℝ):ℂ)
  have hfi : Integrable f μ := by
    have hi : IntegrableOn (fun u : ℝ=>(Real.log u)⁻¹) (Set.Ioc 2 U) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mp
        (goldbach_log_density_continuousOn.mono (by rw [Set.uIcc_of_le hU];exact Set.Icc_subset_Ici_self)).intervalIntegrable
    exact hi.ofReal
  rw [continuous_iff_continuousAt]
  intro n
  change ContinuousAt (fun x : ℝ=>(ℓ:ℂ)⁻¹*(∫ u : ℝ,f u*goldbachLogWindow T ((x-u^2)/ℓ) ∂μ)) n
  apply continuousAt_const.mul
  apply continuousAt_of_dominated (bound:=fun u : ℝ=>‖f u‖*(1/Real.log 2))
  · exact Filter.Eventually.of_forall (fun x=>
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log.inv).mul
        ((goldbach_log_window_measurable T).comp (by fun_prop))).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun x=>Filter.Eventually.of_forall (fun u=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (goldbach_log_window_norm T _) (norm_nonneg _)))
  · exact hfi.norm.mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (Real.sqrt (n-(ℓ:ℝ)*2))),
      ae_restrict_of_ae (volume.ae_ne (Real.sqrt (n-(ℓ:ℝ)*T)))] with u hu hu2 huT
    have hu0 : 0≤u := by linarith [hu.1]
    have hneq (b : ℝ) (hub : u≠Real.sqrt (n-(ℓ:ℝ)*b)) : (n-u^2)/(ℓ:ℝ)≠b := by
      intro he
      have hx := (div_eq_iff hl.ne').mp he
      apply hub
      calc
        u=Real.sqrt (u^2) := (Real.sqrt_sq hu0).symm
        _=Real.sqrt (n-(ℓ:ℝ)*b) := congrArg Real.sqrt (by nlinarith)
    have hc : ContinuousAt (fun x : ℝ=>(x-u^2)/(ℓ:ℝ)) n := by fun_prop
    exact continuousAt_const.mul ((goldbach_log_window_continuousAt T (hneq 2 hu2) (hneq T huT)).comp (f:=fun x : ℝ=>(x-u^2)/(ℓ:ℝ)) hc)

end PrimeSquares
