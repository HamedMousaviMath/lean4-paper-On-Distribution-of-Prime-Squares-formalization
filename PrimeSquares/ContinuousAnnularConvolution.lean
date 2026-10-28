import PrimeSquares.ContinuousAnnularKernelTranslation
import Mathlib.Analysis.Convolution

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def continuousAnnularConvolution (N : ℕ) (β : ℝ) (f : ℝ→ℂ) : ℝ→ℂ :=
  convolution (fun y => Complex.ofReal (continuousAnnularKernel N β y)) f
    (ContinuousLinearMap.mul ℂ ℂ) volume

noncomputable def oneSidedBoxAverage (R : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℝ :=
  (1/R)*(∫ y in Set.Icc 0 R,‖f (x-y)‖)

theorem continuousAnnularConvolution_aestronglyMeasurable {N : ℕ} (hN : 1≤N)
    (β : ℝ) {f : ℝ→ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (continuousAnnularConvolution N β f) volume :=
  (continuousAnnularKernel_complex_integrable hN β).aestronglyMeasurable.convolution (ContinuousLinearMap.mul ℂ ℂ) hf

theorem shiftedL2_integrableOn {f : ℝ→ℂ} (hf : MemLp f 2 volume) (x R : ℝ) :
    IntegrableOn (fun y => f (x-y)) (Set.Icc 0 R) volume := by
  have hc : MemLp (fun y => f (x-y)) 2 volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  exact (hc.locallyIntegrable (by norm_num : (1 : ENNReal)≤2)).integrableOn_isCompact isCompact_Icc

theorem continuousAnnularKernel_product_box {N : ℕ} (hN : 2≤N) {β : ℝ} (hβ1 : β≤1)
    (f : ℝ→ℂ) (x y : ℝ) :
    ‖Complex.ofReal (continuousAnnularKernel N β y)*f (x-y)‖≤
      (1/(N : ℝ)^2)*(Set.Icc 0 ((N : ℝ)^2)).indicator (fun t => ‖f (x-t)‖) y := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (continuousAnnularKernel_nonneg (by omega) β y)]
  have hb := continuousAnnularKernel_box_bound hN hβ1 y
  by_cases hy : y∈Set.Icc 0 ((N : ℝ)^2)
  · rw [Set.indicator_of_mem hy]
    rw [ite_eq_left (show 0≤y ∧ y≤(N : ℝ)^2 from hy)] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · rw [Set.indicator_of_notMem hy]
    rw [ite_eq_right (show ¬(0≤y ∧ y≤(N : ℝ)^2) from hy)] at hb
    have hz : continuousAnnularKernel N β y=0 :=
      le_antisymm hb (continuousAnnularKernel_nonneg (by omega) β y)
    rw [hz,zero_mul,mul_zero]

theorem continuousAnnularConvolution_box_bound {N : ℕ} (hN : 2≤N)
    {β : ℝ} (hβ1 : β≤1) {f : ℝ→ℂ} (hf : MemLp f 2 volume) (x : ℝ) :
    ‖continuousAnnularConvolution N β f x‖≤oneSidedBoxAverage ((N : ℝ)^2) f x := by
  have hin : IntegrableOn (fun y => ‖f (x-y)‖) (Set.Icc 0 ((N : ℝ)^2)) volume :=
    (shiftedL2_integrableOn hf x ((N : ℝ)^2)).norm
  have hb := (hin.integrable_indicator measurableSet_Icc).const_mul (1/(N : ℝ)^2)
  have hmeas : AEStronglyMeasurable
      (fun y => Complex.ofReal (continuousAnnularKernel N β y)*f (x-y)) volume :=
    (continuousAnnularKernel_complex_integrable (by omega) β).aestronglyMeasurable.mul
      (hf.comp_measurePreserving (volume.measurePreserving_sub_left x)).aestronglyMeasurable
  have hi : Integrable (fun y => Complex.ofReal (continuousAnnularKernel N β y)*f (x-y)) volume :=
    hb.mono' hmeas (Filter.Eventually.of_forall (continuousAnnularKernel_product_box hN hβ1 f x))
  change ‖∫ y,Complex.ofReal (continuousAnnularKernel N β y)*f (x-y)‖≤_
  calc
    _ ≤ ∫ y,‖Complex.ofReal (continuousAnnularKernel N β y)*f (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,(1/(N : ℝ)^2)*(Set.Icc 0 ((N : ℝ)^2)).indicator (fun t => ‖f (x-t)‖) y :=
      integral_mono hi.norm hb (continuousAnnularKernel_product_box hN hβ1 f x)
    _ = _ := by
      rw [integral_const_mul,integral_indicator measurableSet_Icc]
      rfl

end PrimeSquares
