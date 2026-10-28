import PrimeSquares.IntervalKernelShiftIntegral
import PrimeSquares.ContinuousAnnularKernelFourier
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem continuousAnnularKernel_integral {N : ℕ} (hN : 1≤N) (β : ℝ) :
    (∫ x,continuousAnnularKernel N β x)=(annularOscillatoryModel N β 0).re := by
  have he := continuousAnnularKernel_fourier hN β 0
  rw [Real.fourier_real_eq_integral_exp_smul] at he
  simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] at he
  rw [integral_complex_ofReal (f := continuousAnnularKernel N β)] at he
  exact congrArg Complex.re he

theorem continuousAnnularKernel_translation_integrable {N : ℕ} (hN : 1≤N)
    (β h : ℝ) :
    Integrable (fun x => |continuousAnnularKernel N β (x-h)-continuousAnnularKernel N β x|) volume := by
  have hf := continuousAnnularKernel_integrable hN β
  have ht : Integrable (fun x => continuousAnnularKernel N β (x-h)) volume :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hf
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using (ht.sub hf).norm

theorem continuousAnnularKernel_translation_rough {N : ℕ} (hN : 1≤N)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (h : ℝ) :
    (∫ x,|continuousAnnularKernel N β (x-h)-continuousAnnularKernel N β x|)≤2 := by
  have hf := continuousAnnularKernel_integrable hN β
  have ht : Integrable (fun x => continuousAnnularKernel N β (x-h)) volume :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hf
  calc
    _ ≤ ∫ x,continuousAnnularKernel N β (x-h)+continuousAnnularKernel N β x := by
      apply integral_mono (continuousAnnularKernel_translation_integrable hN β h) (ht.fun_add hf)
      intro x
      have hb := abs_sub (continuousAnnularKernel N β (x-h)) (continuousAnnularKernel N β x)
      simpa only [abs_of_nonneg (continuousAnnularKernel_nonneg hN β (x-h)),
        abs_of_nonneg (continuousAnnularKernel_nonneg hN β x)] using hb
    _ = 2*(annularOscillatoryModel N β 0).re := by
      rw [integral_add ht hf,integral_sub_right_eq_self,continuousAnnularKernel_integral hN β]
      ring
    _ ≤ 2 := by linarith [(annularMass_re_bounds hN hβ0 hβ1).2]

theorem continuousAnnularKernel_translation_bound {N : ℕ} (hN : 2≤N)
    {β : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (h : ℝ) :
    (∫ x,|continuousAnnularKernel N β (x-h)-continuousAnnularKernel N β x|)≤
      7*|h|/(N : ℝ)^2 := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : 1≤N := by omega
  have hab : (N : ℝ)^2/4≤(N : ℝ)^2 := by nlinarith [sq_nonneg (N : ℝ)]
  have hb : ∀ x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2),|annularKernelDensity N β x|≤1/(N : ℝ)^2 := by
    intro x hx
    have hn : 0≤annularKernelDensity N β x := by
      rw [←continuousAnnularKernel_of_mem hx]
      exact continuousAnnularKernel_nonneg hN1 β x
    rw [abs_of_nonneg hn]
    exact annularKernelDensity_bound hN hβ1 hx
  have he := interval_kernel_shift_integral hab (annularKernelDensity N β)
    (by positivity : 0≤4/(N : ℝ)^4) (by positivity : 0≤1/(N : ℝ)^2)
    (continuousAnnularKernel_integrable hN1 β) hb
    (fun x hx y hy => annularKernelDensity_lipschitz hN hβ0 hβ1 hx hy) h
  refine he.trans_eq ?_
  field_simp
  ring

end PrimeSquares
