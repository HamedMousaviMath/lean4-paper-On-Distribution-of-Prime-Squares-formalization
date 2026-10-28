import PrimeSquares.SchwartzMultiplierRealization
import PrimeSquares.ContinuousAnnularMaximalInterface
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ContDiff ENNReal
namespace PrimeSquares

theorem integrable_convolution_eq_schwartz {K : ℝ → ℂ} (hK : Integrable K volume)
    (f g : SchwartzMap ℝ ℂ)
    (hfg : ∀ θ : ℝ, 𝓕 (g : ℝ → ℂ) θ = 𝓕 K θ * 𝓕 (f : ℝ → ℂ) θ) :
    convolution K (f : ℝ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume = (g : ℝ → ℂ) := by
  let C := convolution K (f : ℝ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume
  have hc : Continuous C := by
    apply BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) _ hK f.continuous
    exact ⟨SchwartzMap.seminorm ℝ 0 0 f, fun _ ⟨x, hx⟩ => hx ▸ SchwartzMap.norm_le_seminorm ℝ f x⟩
  have hi : Integrable C volume := hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) f.integrable
  have hF : 𝓕 C = 𝓕 (g : ℝ → ℂ) := by
    funext θ
    exact (Real.fourier_mul_convolution_eq hK f.integrable θ).trans (hfg θ).symm
  have hFi : Integrable (𝓕 C) volume := by
    rw [hF]
    exact (𝓕 g : SchwartzMap ℝ ℂ).integrable
  calc
    C = 𝓕⁻ (𝓕 C) := (hc.fourierInv_fourier_eq hi hFi).symm
    _ = 𝓕⁻ (𝓕 (g : ℝ → ℂ)) := by rw [hF]
    _ = g := g.continuous.fourierInv_fourier_eq g.integrable (𝓕 g : SchwartzMap ℝ ℂ).integrable

theorem continuousCutoffSymbol_smooth (a : ℝ) :
    ContDiff ℝ ∞ (continuousCutoffSymbol a : ℝ → ℂ) :=
  complexSourceCutoff_smooth.comp (contDiff_const.mul contDiff_id)

theorem continuousCutoffSymbol_boundary {a w : ℝ} (ha : 0 ≤ a) (haw : 1 ≤ a*w)
    (θ : ℝ) (hθ : w ≤ |θ|) : continuousCutoffSymbol a θ = 0 := by
  rw [continuousCutoffSymbol_apply, scaled_cutoff_boundary_zero ha haw hθ, Complex.ofReal_zero]

theorem allAnnularBoundedSymbol_smooth (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (a : ℝ) :
    ContDiff ℝ ∞ (allAnnularBoundedSymbol N hN β hβ0 hβ1 a : ℝ → ℂ) := by
  change ContDiff ℝ ∞ (annularCutoffSymbol N hN β a : ℝ → ℂ)
  exact annularCutoffSymbol_contDiff hN β a

theorem compactSmoothMultiplier_annular_convolution (N : ℕ) (hN : 1 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a : ℝ} (ha : 2 ≤ a)
    (f : SchwartzMap ℝ ℂ) :
    (compactSmoothMultiplier (allAnnularBoundedSymbol N hN β hβ0 hβ1 a)
      (allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1 (by linarith) (by linarith))
      (allAnnularBoundedSymbol_smooth N hN β hβ0 hβ1 a) f : ℝ → ℂ) =
    continuousAnnularConvolution N β
      (compactSmoothMultiplier (continuousCutoffSymbol a)
        (continuousCutoffSymbol_boundary (by linarith : 0 ≤ a) (by linarith : 1 ≤ a*1))
        (continuousCutoffSymbol_smooth a) f : ℝ → ℂ) := by
  apply Eq.symm
  apply integrable_convolution_eq_schwartz (continuousAnnularKernel_complex_integrable hN β)
  intro θ
  rw [compactSmoothMultiplier_fourier, compactSmoothMultiplier_fourier,
    continuousAnnularKernel_fourier hN β θ]
  change annularOscillatoryModel N β θ * Complex.ofReal (sourceArcCutoff (a*θ)) *
    𝓕 (f : ℝ → ℂ) θ = annularOscillatoryModel N β θ *
      (Complex.ofReal (sourceArcCutoff (a*θ)) * 𝓕 (f : ℝ → ℂ) θ)
  ring

theorem finiteCoordinateMaximum_continuous {X : Type*} [TopologicalSpace X]
    (I : Finset ℕ) (u : ℕ → X → ℂ) (hu : ∀ i ∈ I, Continuous (u i)) :
    Continuous (finiteCoordinateMaximum I u) := by
  exact NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun i hi => (hu i hi).nnnorm))

end PrimeSquares
