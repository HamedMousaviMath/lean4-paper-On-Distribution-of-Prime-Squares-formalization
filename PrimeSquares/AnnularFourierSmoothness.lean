import PrimeSquares.ContinuousAnnularKernelFourier
import PrimeSquares.SmoothCutoffSchwartz
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ContDiff
namespace PrimeSquares

theorem continuousAnnularKernel_moments {N : ℕ} (hN : 1≤N) (β : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖^n*‖Complex.ofReal (continuousAnnularKernel N β x)‖) volume := by
  have hc : ContinuousOn (fun x : ℝ => ‖x‖^n*|annularKernelDensity N β x|)
      (Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) :=
    (continuous_norm.pow n).continuousOn.mul (annularKernelDensity_continuousOn hN β).norm
  have hi : Integrable ((Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)).indicator
      (fun x : ℝ => ‖x‖^n*|annularKernelDensity N β x|)) volume :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply hi.congr
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    by_cases hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)
    · simp only [Set.indicator_of_mem hx,continuousAnnularKernel_of_mem hx,
        Complex.norm_real,Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hx,continuousAnnularKernel_of_not_mem hx,
        Complex.ofReal_zero,norm_zero,mul_zero])

theorem annularOscillatoryModel_contDiff {N : ℕ} (hN : 1≤N) (β : ℝ) :
    ContDiff ℝ ∞ (annularOscillatoryModel N β) := by
  have hc := Real.contDiff_fourier (N := ⊤)
    (fun n _ => continuousAnnularKernel_moments hN β n)
  have he : 𝓕 (fun x => Complex.ofReal (continuousAnnularKernel N β x))=
      annularOscillatoryModel N β := by
    funext θ
    exact continuousAnnularKernel_fourier hN β θ
  rw [he] at hc
  exact hc

theorem annularCutoffSymbol_contDiff {N : ℕ} (hN : 1≤N) (β a : ℝ) :
    ContDiff ℝ ∞ (annularCutoffSymbol N hN β a : ℝ→ℂ) := by
  exact (annularOscillatoryModel_contDiff hN β).mul
    (complexSourceCutoff_smooth.comp (contDiff_const.mul contDiff_id))

theorem continuousAnnularSignedSymbol_contDiff (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (J : ℕ) (σ : ℕ→ℂ) :
    ContDiff ℝ ∞ (continuousAnnularSignedSymbol β hβ0 hβ1 a J σ : ℝ→ℂ) := by
  have he : (continuousAnnularSignedSymbol β hβ0 hβ1 a J σ : ℝ→ℂ)=
      fun θ => ∑ j∈Finset.range J,σ j*
        (annularCutoffSymbol ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β a θ-
        annularCutoffSymbol ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β a θ) := by
    funext θ
    simp only [continuousAnnularSignedSymbol,BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.sub_apply,smul_eq_mul,
      allAnnularBoundedSymbol]
    rfl
  rw [he]
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul ((annularCutoffSymbol_contDiff (one_le_pow₀ (by norm_num)) β a).sub
    (annularCutoffSymbol_contDiff (one_le_pow₀ (by norm_num)) β a))

end PrimeSquares
