import PrimeSquares.GoldbachLowerSieveBridge

set_option autoImplicit false
open MeasureTheory Filter
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachLowerArchIntegrand (N n u : ℝ) : ℝ :=
  (Real.log u)⁻¹*(goldbachLogWindow (N^2) (n-u^2)).re

theorem goldbach_lower_arch_integrand_nonneg (N n u : ℝ) (hu : 2≤u) :
    0≤goldbachLowerArchIntegrand N n u := by
  unfold goldbachLowerArchIntegrand goldbachLogWindow
  by_cases hv : n-u^2∈Set.Icc (2:ℝ) (N^2)
  · rw [Set.indicator_of_mem hv,Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg (by linarith)))
      (inv_nonneg.mpr (Real.log_nonneg (by linarith [hv.1])))
  · simp only [Set.indicator_of_notMem hv,Complex.zero_re,mul_zero,le_refl]

theorem goldbach_lower_arch_integrand_integrable (N n : ℝ) :
    IntegrableOn (goldbachLowerArchIntegrand N n) (Set.Icc 2 N) := by
  have hm : Measurable (goldbachLowerArchIntegrand N n) :=
    Real.measurable_log.inv.mul (Complex.continuous_re.measurable.comp
      ((goldbach_log_window_measurable _).comp (measurable_const.sub (measurable_id.pow_const 2))))
  have hi : IntegrableOn (fun _ : ℝ=>(1/Real.log 2)^2) (Set.Icc 2 N) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hu0 : 0<Real.log u := Real.log_pos (by linarith [hu.1])
  have huB : |(Real.log u)⁻¹|≤1/Real.log 2 := by
    rw [abs_of_pos (inv_pos.mpr hu0)]
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.log_pos (by norm_num : (1:ℝ)<2))
      (Real.log_le_log (by norm_num : (0:ℝ)<2) hu.1)
  have hvB := (Complex.abs_re_le_norm (goldbachLogWindow (N^2) (n-u^2))).trans
    (goldbach_log_window_norm (N^2) (n-u^2))
  rw [Real.norm_eq_abs,goldbachLowerArchIntegrand,abs_mul]
  nlinarith [abs_nonneg ((goldbachLogWindow (N^2) (n-u^2)).re),
    abs_nonneg ((Real.log u)⁻¹)]

theorem goldbach_lower_arch_real (N : ℕ) (n : ℝ) :
    (goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re=
      ∫ u in Set.Icc (2:ℝ) (N:ℝ),goldbachLowerArchIntegrand N n u := by
  have he : (fun u : ℝ=>Complex.ofReal ((Real.log u)⁻¹)*
      goldbachLogWindow ((N:ℝ)^2) ((n-u^2)/(1:ℝ)))=
      fun u : ℝ=>(goldbachLowerArchIntegrand N n u:ℂ) := by
    funext u
    dsimp only [goldbachLowerArchIntegrand]
    rw [div_one]
    by_cases hv : n-u^2∈Set.Icc (2:ℝ) ((N:ℝ)^2)
    · simp only [goldbachLogWindow,Set.indicator_of_mem hv,Complex.ofReal_re,Complex.ofReal_mul]
    · simp only [goldbachLogWindow,Set.indicator_of_notMem hv,Complex.zero_re,mul_zero,
        Complex.ofReal_zero]
  unfold goldbachArchimedeanIntegral
  simp only [Nat.cast_one]
  rw [he]
  have hi : (∫ u in Set.Icc (2:ℝ) (N:ℝ),(goldbachLowerArchIntegrand N n u:ℂ))=
      ((∫ u in Set.Icc (2:ℝ) (N:ℝ),goldbachLowerArchIntegrand N n u:ℝ):ℂ) := integral_ofReal
  rw [hi,Complex.ofReal_re]

theorem goldbach_lower_arch_interval (N n u : ℝ) (hN : 0≤N) (hn : 64≤n) (hnN : n≤N^2)
    (hu : u∈Set.Icc (Real.sqrt n/4) (Real.sqrt n/2)) :
    u∈Set.Icc (2:ℝ) N ∧ n-u^2∈Set.Icc (2:ℝ) (N^2) := by
  have hs := Real.sq_sqrt (by linarith : 0≤n)
  have hs0 := Real.sqrt_nonneg n
  have hs8 : 8≤Real.sqrt n := by nlinarith
  have hsN : Real.sqrt n≤N := by nlinarith
  have hu0 : 0≤u := by linarith [hu.1]
  constructor
  · exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  · constructor
    · have hsquared : u^2≤n/4 := by nlinarith [hu.2]
      linarith
    · nlinarith [sq_nonneg u]

theorem goldbach_archimedean_lower (N : ℕ) (hN : 2≤N) (n : ℝ)
    (hn : 64≤n) (hnN : n≤(N:ℝ)^2) :
    Real.sqrt n/(8*(Real.log N)^2)≤
      (goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re := by
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hs : Real.sqrt n/4≤Real.sqrt n/2 := by have := Real.sqrt_nonneg n; linarith
  have hsub : Set.Icc (Real.sqrt n/4) (Real.sqrt n/2)⊆Set.Icc (2:ℝ) (N:ℝ) :=
    fun u hu=>(goldbach_lower_arch_interval N n u hN0 hn hnN hu).1
  have hfi := goldbach_lower_arch_integrand_integrable N n
  have hfsmall := hfi.mono_set hsub
  have hpoint : ∀ u∈Set.Icc (Real.sqrt n/4) (Real.sqrt n/2),
      1/(2*(Real.log N)^2)≤goldbachLowerArchIntegrand N n u := by
    intro u hu
    obtain ⟨huN,hv⟩ := goldbach_lower_arch_interval N n u hN0 hn hnN hu
    have hlu : 0<Real.log u := Real.log_pos (by linarith [huN.1])
    have hlv : 0<Real.log (n-u^2) := Real.log_pos (by linarith [hv.1])
    have hLu : Real.log u≤Real.log N := Real.log_le_log (by linarith [huN.1]) huN.2
    have hLv : Real.log (n-u^2)≤2*Real.log N := by
      have hh := Real.log_le_log (by linarith [hv.1]) hv.2
      rwa [Real.log_pow] at hh
    have hprod : Real.log u*Real.log (n-u^2)≤2*(Real.log N)^2 := by nlinarith
    have hh := one_div_le_one_div_of_le (mul_pos hlu hlv) hprod
    simpa only [goldbachLowerArchIntegrand,goldbachLogWindow,Set.indicator_of_mem hv,
      Complex.ofReal_re,one_div,mul_inv] using hh
  have hsmall := setIntegral_ge_of_const_le_real measurableSet_Icc
    isCompact_Icc.measure_ne_top hpoint hfsmall
  have hext := setIntegral_mono_set hfi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact goldbach_lower_arch_integrand_nonneg N n u hu.1) hsub.eventuallyLE
  rw [goldbach_lower_arch_real]
  apply le_trans _ (hsmall.trans hext)
  rw [Real.volume_real_Icc_of_le hs]
  field_simp
  norm_num

end PrimeSquares
