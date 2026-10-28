import PrimeSquares.ContinuousAnnularKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
namespace PrimeSquares

theorem annularKernelDensity_lipschitz {N : ℕ} (hN : 2≤N) {β x y : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1)
    (hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2))
    (hy : y∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) :
    |annularKernelDensity N β x-annularKernelDensity N β y|≤
      (4/(N : ℝ)^4)*|x-y| := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpos : ∀ z∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2),0<z :=
    fun z hz => (by positivity : (0 : ℝ)<(N : ℝ)^2/4).trans_le hz.1
  have hf : ∀ z∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2),DifferentiableAt ℝ (annularKernelDensity N β) z :=
    fun z hz => (annularKernelDensity_hasDerivAt N β (hpos z hz)).differentiableAt
  have hb : ∀ z∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2),‖deriv (annularKernelDensity N β) z‖≤4/(N : ℝ)^4 := by
    intro z hz
    rw [(annularKernelDensity_hasDerivAt N β (hpos z hz)).deriv,Real.norm_eq_abs]
    exact annularKernelDerivative_bound hN hβ0 hβ1 hz
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc _ _) hy hx

theorem continuousAnnularKernel_far_zero (N : ℕ) (β : ℝ) {h x : ℝ}
    (hsmall : (N : ℝ)^2≤ |h|) (hfar : 2*|h|< |x|) :
    continuousAnnularKernel N β x=0 ∧ continuousAnnularKernel N β (x-h)=0 := by
  constructor
  · apply continuousAnnularKernel_of_not_mem
    intro hx
    have hx0 : 0≤x := (by positivity : (0 : ℝ)≤(N : ℝ)^2/4).trans hx.1
    rw [abs_of_nonneg hx0] at hfar
    nlinarith [abs_nonneg h,hx.2]
  · apply continuousAnnularKernel_of_not_mem
    intro hx
    have hx0 : 0≤x-h := (by positivity : (0 : ℝ)≤(N : ℝ)^2/4).trans hx.1
    have ht := abs_add_le (x-h) h
    rw [sub_add_cancel,abs_of_nonneg hx0] at ht
    nlinarith [hx.2]

end PrimeSquares
