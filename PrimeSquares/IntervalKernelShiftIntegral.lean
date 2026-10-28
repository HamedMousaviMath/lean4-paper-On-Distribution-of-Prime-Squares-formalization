import PrimeSquares.IntervalKernelShiftGeometry
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem intervalKernelShiftEnvelope_integrable (a b L B h : ℝ) :
    Integrable (intervalKernelShiftEnvelope a b L B h) volume := by
  have hi (c d : ℝ) : Integrable ((Set.Icc c d).indicator (fun _ => (1 : ℝ))) volume :=
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne) : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc c d) volume).integrable_indicator measurableSet_Icc
  exact ((hi a b).const_mul (L*|h|)).add
    (((hi (a-|h|) (a+|h|)).add (hi (b-|h|) (b+|h|))).const_mul B)

theorem intervalKernelShiftEnvelope_integral {a b : ℝ} (hab : a≤b) (L B h : ℝ) :
    (∫ x,intervalKernelShiftEnvelope a b L B h x)=
      (L*(b-a)+4*B)*|h| := by
  have hi (c d : ℝ) : Integrable ((Set.Icc c d).indicator (fun _ => (1 : ℝ))) volume :=
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne) : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc c d) volume).integrable_indicator measurableSet_Icc
  have hac : a-|h|≤a+|h| := by linarith [abs_nonneg h]
  have hbc : b-|h|≤b+|h| := by linarith [abs_nonneg h]
  change (∫ x,L*|h| *(Set.Icc a b).indicator (fun _ => (1 : ℝ)) x +
    B*((Set.Icc (a-|h|) (a+|h|)).indicator (fun _ => (1 : ℝ)) x +
      (Set.Icc (b-|h|) (b+|h|)).indicator (fun _ => (1 : ℝ)) x))=_
  have hsum : Integrable (fun x =>
      (Set.Icc (a-|h|) (a+|h|)).indicator (fun _ => (1 : ℝ)) x +
      (Set.Icc (b-|h|) (b+|h|)).indicator (fun _ => (1 : ℝ)) x) volume := by
    exact (hi (a-|h|) (a+|h|)).fun_add (hi (b-|h|) (b+|h|))
  rw [integral_add ((hi a b).const_mul (L*|h|)) (hsum.const_mul B)]
  rw [integral_const_mul,integral_const_mul,
    integral_add (hi (a-|h|) (a+|h|)) (hi (b-|h|) (b+|h|))]
  simp only [integral_indicator_const,measurableSet_Icc,smul_eq_mul,mul_one,
    Real.volume_real_Icc_of_le hab,Real.volume_real_Icc_of_le hac,
    Real.volume_real_Icc_of_le hbc]
  ring

theorem interval_kernel_shift_integral {a b L B : ℝ} (hab : a≤b) (f : ℝ→ℝ)
    (hL : 0≤L) (hB : 0≤B)
    (hf : Integrable ((Set.Icc a b).indicator f) volume)
    (hb : ∀ x∈Set.Icc a b,|f x|≤B)
    (hl : ∀ x∈Set.Icc a b,∀ y∈Set.Icc a b,|f x-f y|≤L*|x-y|)
    (h : ℝ) :
    (∫ x,|(Set.Icc a b).indicator f (x-h)-(Set.Icc a b).indicator f x|)≤
      (L*(b-a)+4*B)*|h| := by
  have ht : Integrable (fun x => (Set.Icc a b).indicator f (x-h)) volume :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hf
  have hd : Integrable (fun x => |(Set.Icc a b).indicator f (x-h)-
      (Set.Icc a b).indicator f x|) volume := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (ht.sub hf).norm
  calc
    _ ≤ ∫ x,intervalKernelShiftEnvelope a b L B h x :=
      integral_mono hd (intervalKernelShiftEnvelope_integrable a b L B h)
        (interval_kernel_shift_envelope f hL hB hb hl h)
    _ = _ := intervalKernelShiftEnvelope_integral hab L B h

end PrimeSquares
