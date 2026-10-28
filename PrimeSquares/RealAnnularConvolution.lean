import PrimeSquares.RealAnnularKernelBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Topology
namespace PrimeSquares

theorem shiftedLp_integrableOn {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f p volume) (x a b : ℝ) :
    IntegrableOn (fun y => f (x-y)) (Set.Icc a b) volume := by
  have hc := hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  exact (hc.locallyIntegrable hp).integrableOn_isCompact isCompact_Icc

theorem realContinuousAnnularKernel_product_box {N β : ℝ} (hN : 2 ≤ N) (hβ : β ≤ 1)
    (f : ℝ → ℂ) (x y : ℝ) :
    ‖Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y)‖ ≤
      (1/N^2)*(Set.Icc 0 (N^2)).indicator (fun t => ‖f (x-t)‖) y := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (realContinuousAnnularKernel_nonneg (by linarith) β y)]
  have hb := realContinuousAnnularKernel_box_bound hN hβ y
  by_cases hy : y∈Set.Icc 0 (N^2)
  · rw [Set.indicator_of_mem hy]
    rw [ite_eq_left (show 0 ≤ y ∧ y ≤ N^2 from hy)] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · rw [Set.indicator_of_notMem hy]
    rw [ite_eq_right (show ¬ (0 ≤ y ∧ y ≤ N^2) from hy)] at hb
    have hz : realContinuousAnnularKernel N β y=0 :=
      le_antisymm hb (realContinuousAnnularKernel_nonneg (by linarith) β y)
    rw [hz,zero_mul,mul_zero]

theorem realContinuousAnnularConvolution_box_bound {N β : ℝ} (hN : 2 ≤ N) (hβ : β ≤ 1)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f p volume) (x : ℝ) :
    ‖realContinuousAnnularConvolution N β f x‖ ≤ oneSidedBoxAverage (N^2) f x := by
  have hin : IntegrableOn (fun y => ‖f (x-y)‖) (Set.Icc 0 (N^2)) volume :=
    (shiftedLp_integrableOn hp hf x 0 (N^2)).norm
  have hb := (hin.integrable_indicator measurableSet_Icc).const_mul (1/N^2)
  have hmeas : AEStronglyMeasurable
      (fun y => Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y)) volume :=
    (realContinuousAnnularKernel_complex_integrable (by linarith) β).aestronglyMeasurable.mul
      (hf.comp_measurePreserving (volume.measurePreserving_sub_left x)).aestronglyMeasurable
  have hi : Integrable (fun y => Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y)) volume :=
    hb.mono' hmeas (Filter.Eventually.of_forall (realContinuousAnnularKernel_product_box hN hβ f x))
  change ‖∫ y,Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y)‖ ≤ _
  calc
    _ ≤ ∫ y,‖Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,(1/N^2)*(Set.Icc 0 (N^2)).indicator (fun t => ‖f (x-t)‖) y :=
      integral_mono hi.norm hb (realContinuousAnnularKernel_product_box hN hβ f x)
    _ = _ := by rw [integral_const_mul,integral_indicator measurableSet_Icc];rfl

theorem realContinuousAnnularConvolution_aestronglyMeasurable {N : ℝ} (hN : 0 < N)
    (β : ℝ) {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (realContinuousAnnularConvolution N β f) volume :=
  (realContinuousAnnularKernel_complex_integrable hN β).aestronglyMeasurable.convolution
    (ContinuousLinearMap.mul ℂ ℂ) hf

noncomputable def realAnnularPrimitiveIntegrand (β : ℝ) (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  Complex.ofReal ((max y 1)^(β/2-1))*f (x-y)

theorem realAnnularPrimitiveIntegrand_locallyIntegrable {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℝ → ℂ} (hf : MemLp f p volume) (β x : ℝ) :
    LocallyIntegrable (realAnnularPrimitiveIntegrand β f x) volume := by
  have hw : Continuous (fun y : ℝ => Complex.ofReal ((max y 1)^(β/2-1))) := by
    apply Complex.continuous_ofReal.comp
    apply Continuous.rpow_const (continuous_id.max continuous_const)
    intro y
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right y 1)))
  exact ((hf.comp_measurePreserving (volume.measurePreserving_sub_left x)).locallyIntegrable hp).continuous_mul hw

theorem realContinuousAnnularConvolution_interval {N : ℝ} (hN : 2 ≤ N) (β : ℝ)
    (f : ℝ → ℂ) (x : ℝ) :
    realContinuousAnnularConvolution N β f x=
      Complex.ofReal (1/(2*N))*∫ y in N^2/4..N^2, realAnnularPrimitiveIntegrand β f x y := by
  have he : (fun y => Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y))=
      (Set.Icc (N^2/4) (N^2)).indicator
        (fun y => Complex.ofReal (1/(2*N))*realAnnularPrimitiveIntegrand β f x y) := by
    funext y
    by_cases hy : y∈Set.Icc (N^2/4) (N^2)
    · have hy1 : 1 ≤ y := by nlinarith [hy.1]
      simp only [realContinuousAnnularKernel,Set.indicator_of_mem hy,realAnnularKernelDensity,
        realAnnularPrimitiveIntegrand,max_eq_left hy1,Complex.ofReal_div,Complex.ofReal_mul,
        Complex.ofReal_one]
      ring
    · simp only [realContinuousAnnularKernel,Set.indicator_of_notMem hy,Complex.ofReal_zero,zero_mul]
  change (∫ y,Complex.ofReal (realContinuousAnnularKernel N β y)*f (x-y))=_
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by nlinarith [sq_nonneg N] : N^2/4 ≤ N^2),
    intervalIntegral.integral_const_mul]

theorem realContinuousAnnularConvolution_continuous_scale (β : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f p volume) (x : ℝ) :
    Continuous (fun N : Set.Ici (2:ℝ) => realContinuousAnnularConvolution N.val β f x) := by
  have hi := realAnnularPrimitiveIntegrand_locallyIntegrable hp hf β x
  have hI (a b : ℝ) : IntervalIntegrable (realAnnularPrimitiveIntegrand β f x) volume a b :=
    (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hprim := intervalIntegral.continuous_primitive hI 1
  have he (N : Set.Ici (2:ℝ)) : realContinuousAnnularConvolution N.val β f x=
      Complex.ofReal (1/(2*N.val))*
        ((∫ y in 1..N.val^2,realAnnularPrimitiveIntegrand β f x y)-
          ∫ y in 1..N.val^2/4,realAnnularPrimitiveIntegrand β f x y) := by
    rw [realContinuousAnnularConvolution_interval N.property β f x]
    congr 1
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hI 1 (N.val^2/4)) (hI (N.val^2/4) (N.val^2))
    exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hadj))
  simp_rw [he]
  have hN0 : ∀ N : Set.Ici (2:ℝ), (2:ℝ)*N.val ≠ 0 := by
    intro N
    have h : (2:ℝ) ≤ N.val := N.property
    exact mul_ne_zero (by norm_num) (ne_of_gt (by linarith))
  exact (Complex.continuous_ofReal.comp (continuous_const.div
    (continuous_const.mul continuous_subtype_val) hN0)).mul
      ((hprim.comp (continuous_subtype_val.pow 2)).sub
        (hprim.comp ((continuous_subtype_val.pow 2).div_const 4)))

end PrimeSquares
