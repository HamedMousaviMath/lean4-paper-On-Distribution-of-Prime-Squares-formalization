import PrimeSquares.SchwartzAnnularMaximum
import PrimeSquares.CyclicLiftCharacters
import PrimeSquares.AnnularCutoffRemainderBounds

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ContDiff ENNReal
namespace PrimeSquares

theorem schwartz_eq_of_fourier {f g : SchwartzMap ℝ ℂ}
    (h : ∀ θ : ℝ, 𝓕 (f : ℝ → ℂ) θ = 𝓕 (g : ℝ → ℂ) θ) : f = g := by
  have hF : (𝓕 f : SchwartzMap ℝ ℂ) = (𝓕 g : SchwartzMap ℝ ℂ) := by
    ext θ
    exact h θ
  have hi := congrArg (fun v : SchwartzMap ℝ ℂ => (𝓕⁻ v : SchwartzMap ℝ ℂ)) hF
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi

theorem cyclicSynthesisSchwartz_fourier (Γ : Finset ℚ) (P : ℕ)
    (u : ℚ → SchwartzMap ℝ ℂ) (y : ZMod P) (θ : ℝ) :
    𝓕 (cyclicSynthesisSchwartz Γ P u y : ℝ → ℂ) θ =
      ∑ α ∈ Γ, negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle) *
        𝓕 (u α : ℝ → ℂ) θ := by
  have hF : (𝓕 (cyclicSynthesisSchwartz Γ P u y) : SchwartzMap ℝ ℂ) =
      ∑ α ∈ Γ, negativeFourierCharacter (-(y.val : ℤ)) ((α : ℝ) : PrimeCircle) •
        (𝓕 (u α) : SchwartzMap ℝ ℂ) := by
    simp only [cyclicSynthesisSchwartz, FourierTransform.fourier_sum,
      FourierTransform.fourier_smul]
  have h := congrArg (fun v : SchwartzMap ℝ ℂ => v θ) hF
  simpa only [SchwartzMap.fourier_coe, _root_.sum_apply, _root_.smul_apply, smul_eq_mul] using h

theorem cyclicSynthesis_weighted_convolution (Γ : Finset ℚ) (P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ Γ, α.den ∣ P) (ν : ZMod P → ℂ) (u : ℚ → SchwartzMap ℝ ℂ)
    (y : ZMod P) :
    cyclicSynthesisSchwartz Γ P (fun α => cyclicRationalCoefficient P ν α • u α) y =
      cyclicConvolutionSchwartz P ν (cyclicSynthesisSchwartz Γ P u) y := by
  ext x
  rw [cyclicSynthesisSchwartz_apply, cyclicSynthesis_convolution Γ P hΓ]
  simp only [cyclicSynthesis, _root_.smul_apply, smul_eq_mul]

theorem compactSmoothMultiplier_synthesis (Γ : Finset ℚ) (P : ℕ)
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) (u v : ℚ → SchwartzMap ℝ ℂ)
    (huv : ∀ α ∈ Γ, ∀ θ : ℝ, 𝓕 (v α : ℝ → ℂ) θ = m θ * 𝓕 (u α : ℝ → ℂ) θ)
    (y : ZMod P) :
    compactSmoothMultiplier m hs hm (cyclicSynthesisSchwartz Γ P u y) =
      cyclicSynthesisSchwartz Γ P v y := by
  apply schwartz_eq_of_fourier
  intro θ
  rw [compactSmoothMultiplier_fourier, cyclicSynthesisSchwartz_fourier,
    cyclicSynthesisSchwartz_fourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [huv α hα θ]
  ring

theorem annular_symbol_absorbs_wide_cutoff (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : 2*a ≤ b) (θ : ℝ) :
    allAnnularBoundedSymbol N hN β hβ0 hβ1 b θ * continuousCutoffSymbol a θ =
      allAnnularBoundedSymbol N hN β hβ0 hβ1 b θ := by
  rw [allAnnularBoundedSymbol_apply, continuousCutoffSymbol_apply]
  have hη := sourceArcCutoff_nested_product ha hb hab θ
  have hc : Complex.ofReal (sourceArcCutoff (a*θ)) * Complex.ofReal (sourceArcCutoff (b*θ)) =
      Complex.ofReal (sourceArcCutoff (b*θ)) := by rw [←Complex.ofReal_mul, hη]
  calc
    _ = annularOscillatoryModel N β θ *
      (Complex.ofReal (sourceArcCutoff (a*θ))*Complex.ofReal (sourceArcCutoff (b*θ))) := by ring
    _ = _ := by rw [hc]

theorem schwartz_smul_fourier (c : ℂ) (u : SchwartzMap ℝ ℂ) (θ : ℝ) :
    𝓕 ((c • u : SchwartzMap ℝ ℂ) : ℝ → ℂ) θ = c * 𝓕 (u : ℝ → ℂ) θ := by
  have h := congrArg (fun v : SchwartzMap ℝ ℂ => v θ) (FourierTransform.fourier_smul c u)
  simpa only [SchwartzMap.fourier_coe, _root_.smul_apply, smul_eq_mul] using h

end PrimeSquares
