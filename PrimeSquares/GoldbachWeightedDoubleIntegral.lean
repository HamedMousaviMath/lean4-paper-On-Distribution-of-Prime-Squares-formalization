import PrimeSquares.GoldbachWeightedMellin
import PrimeSquares.GoldbachWeightedLogComparisons
import PrimeSquares.GoldbachWeightedDoubleGeometry

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_log_harmonic_integral_le (a b : ℝ) (ha : 2≤a) (hab : a≤b) :
    (∫ u in Set.Icc a b,1/(u*Real.sqrt (Real.log u)))≤
      (Real.log b-Real.log a)/Real.sqrt (Real.log a) := by
  have hloga : 0<Real.log a := Real.log_pos (by linarith)
  have hcont : ContinuousOn (fun u : ℝ=>1/(u*Real.sqrt (Real.log u))) (Set.Icc a b) := by
    intro u hu
    have hu0 : u≠0 := by linarith [hu.1]
    have hs : Real.sqrt (Real.log u)≠0 :=
      (Real.sqrt_pos.mpr (Real.log_pos (by linarith [hu.1]))).ne'
    have hd := mul_ne_zero hu0 hs
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hbase : ContinuousOn (fun u : ℝ=>1/u) (Set.Icc a b) := by
    intro u hu
    have hu0 : u≠0 := by linarith [hu.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hh : (∫ u in Set.Icc a b,1/(u*Real.sqrt (Real.log u)))≤
      (∫ u in Set.Icc a b,(1/Real.sqrt (Real.log a))*(1/u)) := by
    apply integral_mono_ae hcont.integrableOn_Icc (hbase.integrableOn_Icc.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : 0<u := by linarith [hu.1]
    have hlogs := Real.log_le_log (by linarith : 0<a) hu.1
    have hs := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hloga) (Real.sqrt_le_sqrt hlogs)
    have hm := mul_le_mul_of_nonneg_right hs (one_div_nonneg.mpr hu0.le)
    convert hm using 1;ring
  have hi : (∫ u in Set.Icc a b,1/u)=Real.log b-Real.log a := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le hab] at hu
      simpa only [one_div] using Real.hasDerivAt_log (show u≠0 by linarith [hu.1])
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hbase.integrableOn_Icc
  rw [integral_const_mul,hi] at hh
  convert hh using 1;ring

theorem goldbach_weighted_double_integrands_continuous (D a : ℝ) (hD : 18≤D)
    (ha : 2≤a) :
    ContinuousOn (fun u : ℝ=>goldbachWeightedInnerIntegral (Real.log (2*u)/D))
      (Set.Icc a (Real.exp (D/9)/2)) ∧
    ContinuousOn (fun u : ℝ=>1/(u*Real.sqrt (Real.log u)))
      (Set.Icc a (Real.exp (D/9)/2)) ∧
    ContinuousOn (fun u : ℝ=>1/(u*Real.sqrt (Real.log (2*u))))
      (Set.Icc a (Real.exp (D/9)/2)) := by
  let S := Set.Icc a (Real.exp (D/9)/2)
  have hr : ContinuousOn (fun u : ℝ=>Real.log (2*u)/D) S := by
    intro u hu
    have hu0 : 0<u := by linarith [hu.1]
    have h₂ : 2*u≠0 := mul_ne_zero (by norm_num) hu0.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hJ := goldbach_weighted_inner_continuous.comp hr (by
    intro u hu
    have hg := goldbach_weighted_double_u_geometry D a u hD ha hu
    exact ⟨hg.1.le,hg.2.1⟩)
  refine ⟨hJ,?_,?_⟩ <;> intro u hu
  · have hu0 : u≠0 := by linarith [hu.1]
    have hs : Real.sqrt (Real.log u)≠0 :=
      (Real.sqrt_pos.mpr (Real.log_pos (by linarith [hu.1]))).ne'
    have hd := mul_ne_zero hu0 hs
    apply ContinuousAt.continuousWithinAt
    fun_prop
  · have hu0 : 0<u := by linarith [hu.1]
    have h₂ : 2*u≠0 := mul_ne_zero (by norm_num) hu0.ne'
    have hs : Real.sqrt (Real.log (2*u))≠0 :=
      (Real.sqrt_pos.mpr (Real.log_pos (by linarith [hu.1]))).ne'
    have hd := mul_ne_zero hu0.ne' hs
    apply ContinuousAt.continuousWithinAt
    fun_prop

theorem goldbach_weighted_double_integral_le_W (D a : ℝ) (hD : 18≤D) (ha : 2≤a)
    (haU : a≤Real.exp (D/9)/2) :
    (∫ u in Set.Icc a (Real.exp (D/9)/2),
      goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log u)))≤
      Real.sqrt (1+Real.log 2/Real.log a)*Real.sqrt D*
        (8*Real.sqrt 2*goldbachWeightedW (9/8)) := by
  have hD0 : 0<D := by linarith
  have ha0 : 0<a := by linarith
  have hcont := goldbach_weighted_double_integrands_continuous D a hD ha
  have hleft : IntegrableOn (fun u : ℝ=>goldbachWeightedInnerIntegral (Real.log (2*u)/D)/
      (u*Real.sqrt (Real.log u))) (Set.Icc a (Real.exp (D/9)/2)) := by
    apply (hcont.1.mul hcont.2.1).integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro u hu
    dsimp only [Pi.mul_apply]
    ring
  have hright : IntegrableOn (fun u : ℝ=>goldbachWeightedInnerIntegral (Real.log (2*u)/D)/
      (u*Real.sqrt (Real.log (2*u)))) (Set.Icc a (Real.exp (D/9)/2)) := by
    apply (hcont.1.mul hcont.2.2).integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro u hu
    dsimp only [Pi.mul_apply]
    ring
  let F := Real.sqrt (1+Real.log 2/Real.log a)
  have hp : (∫ u in Set.Icc a (Real.exp (D/9)/2),
      goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log u)))≤
      F*(∫ u in Set.Icc a (Real.exp (D/9)/2),
        goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log (2*u)))) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hleft (hright.const_mul F)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hg := goldbach_weighted_double_u_geometry D a u hD ha hu
    have hJ := goldbach_weighted_inner_nonneg (Real.log (2*u)/D) hg.2.1
    have hu0 : 0<u := by linarith [hu.1]
    have hh := mul_le_mul_of_nonneg_left (goldbach_weighted_log_offset a u ha hu.1)
      (div_nonneg hJ hu0.le)
    convert hh using 1 <;> ring
  have hr := goldbach_weighted_double_u_geometry D a a hD ha ⟨le_rfl,haU⟩
  have he : Real.exp (D*(Real.log (2*a)/D))/2=a := by
    rw [mul_div_cancel₀ _ hD0.ne',Real.exp_log (show 0<2*a by positivity)]
    ring
  have hm := goldbach_weighted_outer_mellin_le_W D (Real.log (2*a)/D) hD0 hr.1 hr.2.1
  rw [he] at hm
  rw [intervalIntegral.integral_of_le haU,←integral_Icc_eq_integral_Ioc] at hm
  have hh := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (1+Real.log 2/Real.log a))
  apply hp.trans
  convert hh using 1;ring

end PrimeSquares
