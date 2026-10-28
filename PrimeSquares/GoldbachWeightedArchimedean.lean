import PrimeSquares.GoldbachWeightedThinWindow

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedArchIntegrand (N : ℝ) (ℓ : ℕ) (n u : ℝ) : ℝ :=
  (Real.log u)⁻¹*(goldbachLogWindow (N^2) ((n-u^2)/(ℓ:ℝ))).re

theorem goldbach_weighted_arch_integrand_integrable (N n : ℝ) (ℓ : ℕ) :
    IntegrableOn (goldbachWeightedArchIntegrand N ℓ n) (Set.Icc 2 N) := by
  have hm : Measurable (goldbachWeightedArchIntegrand N ℓ n) :=
    Real.measurable_log.inv.mul (Complex.continuous_re.measurable.comp
      ((goldbach_log_window_measurable _).comp
        ((measurable_const.sub (measurable_id.pow_const 2)).div_const (ℓ:ℝ))))
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
  have hvB := (Complex.abs_re_le_norm (goldbachLogWindow (N^2) ((n-u^2)/(ℓ:ℝ)))).trans
    (goldbach_log_window_norm (N^2) ((n-u^2)/(ℓ:ℝ)))
  rw [Real.norm_eq_abs,goldbachWeightedArchIntegrand,abs_mul]
  nlinarith [abs_nonneg ((goldbachLogWindow (N^2) ((n-u^2)/(ℓ:ℝ))).re),
    abs_nonneg ((Real.log u)⁻¹)]

theorem goldbach_weighted_arch_real (N ℓ : ℕ) (n : ℝ) :
    (goldbachArchimedeanIntegral ℓ n (N:ℝ) ((N:ℝ)^2)).re=
      ∫ u in Set.Icc (2:ℝ) (N:ℝ),goldbachWeightedArchIntegrand N ℓ n u := by
  have he : (fun u : ℝ=>Complex.ofReal ((Real.log u)⁻¹)*
      goldbachLogWindow ((N:ℝ)^2) ((n-u^2)/(ℓ:ℝ)))=
      fun u : ℝ=>(goldbachWeightedArchIntegrand N ℓ n u:ℂ) := by
    funext u
    dsimp only [goldbachWeightedArchIntegrand]
    by_cases hv : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) ((N:ℝ)^2)
    · simp only [goldbachLogWindow,Set.indicator_of_mem hv,Complex.ofReal_re,Complex.ofReal_mul]
    · simp only [goldbachLogWindow,Set.indicator_of_notMem hv,Complex.zero_re,mul_zero,
        Complex.ofReal_zero]
  unfold goldbachArchimedeanIntegral
  rw [he]
  have hi : (∫ u in Set.Icc (2:ℝ) (N:ℝ),(goldbachWeightedArchIntegrand N ℓ n u:ℂ))=
      ((∫ u in Set.Icc (2:ℝ) (N:ℝ),goldbachWeightedArchIntegrand N ℓ n u:ℝ):ℂ) := integral_ofReal
  rw [hi,Complex.ofReal_re]

theorem goldbach_weighted_arch_sum_identity {ι : Type*} (I : Finset ι)
    (N : ℕ) (ℓ : ι→ℕ) (c : ι→ℝ) (n : ℝ) :
    (∑ i∈I,c i*(goldbachArchimedeanIntegral (ℓ i) n (N:ℝ) ((N:ℝ)^2)).re)=
      ∫ u in Set.Icc (2:ℝ) (N:ℝ),∑ i∈I,c i*goldbachWeightedArchIntegrand N (ℓ i) n u := by
  classical
  have hi (i : ι) (_hi : i∈I) :
      IntegrableOn (fun u : ℝ=>c i*goldbachWeightedArchIntegrand N (ℓ i) n u) (Set.Icc (2:ℝ) (N:ℝ)) :=
    (goldbach_weighted_arch_integrand_integrable N n (ℓ i)).const_mul (c i)
  rw [integral_finsetSum I hi]
  apply sum_congr rfl
  intro i hiI
  rw [integral_const_mul,goldbach_weighted_arch_real]

theorem goldbach_weighted_arch_integrand_nonneg (N n u : ℝ) (ℓ : ℕ) (hu : 2≤u) :
    0≤goldbachWeightedArchIntegrand N ℓ n u := by
  unfold goldbachWeightedArchIntegrand goldbachLogWindow
  by_cases hv : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) (N^2)
  · rw [Set.indicator_of_mem hv,Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg (by linarith)))
      (inv_nonneg.mpr (Real.log_nonneg (by linarith [hv.1])))
  · simp only [Set.indicator_of_notMem hv,Complex.zero_re,mul_zero,le_refl]

end PrimeSquares
