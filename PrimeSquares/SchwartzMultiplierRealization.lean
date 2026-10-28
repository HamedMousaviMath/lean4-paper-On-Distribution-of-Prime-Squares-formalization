import PrimeSquares.FiniteSmoothFourierLift
import PrimeSquares.CyclicRealLpBounds

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ContDiff ENNReal
namespace PrimeSquares

theorem realLineFourier_schwartz (f : SchwartzMap ℝ ℂ) :
    realLineFourier (f.toLp 2) = (𝓕 f : SchwartzMap ℝ ℂ).toLp 2 := by
  change 𝓕 (f.toLp 2) = _
  exact SchwartzMap.toLp_fourier_eq f

theorem realLineMultiplier_schwartz_of_fourier (m : BoundedContinuousFunction ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ)
    (hfg : ∀ θ : ℝ, 𝓕 (g : ℝ → ℂ) θ = m θ * 𝓕 (f : ℝ → ℂ) θ) :
    realLineMultiplier m (f.toLp 2) = g.toLp 2 := by
  apply realLineFourier.injective
  rw [realLineFourier_multiplier, realLineFourier_schwartz, realLineFourier_schwartz]
  apply Lp.ext
  filter_upwards [realLineMultiply_ae m ((𝓕 f : SchwartzMap ℝ ℂ).toLp 2),
    (𝓕 f : SchwartzMap ℝ ℂ).coeFn_toLp 2, (𝓕 g : SchwartzMap ℝ ℂ).coeFn_toLp 2] with θ hprod hf hg
  rw [hprod, hf, hg]
  exact (hfg θ).symm

theorem realLpMultiplierBound_on_schwartz {p : ℝ≥0∞} {K : ℝ}
    (m : BoundedContinuousFunction ℝ ℂ) (H : RealLpMultiplierBound p m K)
    (f g : SchwartzMap ℝ ℂ)
    (hfg : ∀ θ : ℝ, 𝓕 (g : ℝ → ℂ) θ = m θ * 𝓕 (f : ℝ → ℂ) θ) :
    eLpNorm (g : ℝ → ℂ) p volume ≤ ENNReal.ofReal K * eLpNorm (f : ℝ → ℂ) p volume := by
  have hfin : MemLp (f.toLp 2 : ℝ → ℂ) p volume :=
    (f.memLp p).ae_eq (f.coeFn_toLp 2).symm
  obtain ⟨_, hn⟩ := H (f.toLp 2) hfin
  rw [realLineMultiplier_schwartz_of_fourier m f g hfg,
    eLpNorm_congr_ae (p := p) (g.coeFn_toLp 2 volume),
    eLpNorm_congr_ae (p := p) (f.coeFn_toLp 2 volume)] at hn
  exact hn

noncomputable def compactSymbolProduct (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ((compact_support_of_unit_boundary hs).mul_right :
    HasCompactSupport (fun θ : ℝ => m θ * (𝓕 f : SchwartzMap ℝ ℂ) θ)).toSchwartzMap
      (hm.mul ((𝓕 f : SchwartzMap ℝ ℂ).smooth ⊤))

noncomputable def compactSmoothMultiplier (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (compactSymbolProduct m hs hm f)

theorem compactSmoothMultiplier_fourier (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (f : SchwartzMap ℝ ℂ) (θ : ℝ) :
    𝓕 (compactSmoothMultiplier m hs hm f : ℝ → ℂ) θ = m θ * 𝓕 (f : ℝ → ℂ) θ := by
  have hF : (𝓕 (𝓕⁻ (compactSymbolProduct m hs hm f) : SchwartzMap ℝ ℂ) :
      SchwartzMap ℝ ℂ) = compactSymbolProduct m hs hm f := FourierTransform.fourier_fourierInv_eq _
  have he := congrArg (fun v : SchwartzMap ℝ ℂ => v θ) hF
  have ha : compactSymbolProduct m hs hm f θ = m θ * (𝓕 f : SchwartzMap ℝ ℂ) θ := rfl
  rw [ha] at he
  simpa only [compactSmoothMultiplier, SchwartzMap.fourier_coe] using he

theorem compactSmoothMultiplier_Lp {p : ℝ≥0∞} {K : ℝ}
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) (H : RealLpMultiplierBound p m K)
    (f : SchwartzMap ℝ ℂ) :
    eLpNorm (compactSmoothMultiplier m hs hm f : ℝ → ℂ) p volume ≤
      ENNReal.ofReal K * eLpNorm (f : ℝ → ℂ) p volume :=
  realLpMultiplierBound_on_schwartz m H f _ (compactSmoothMultiplier_fourier m hs hm f)

theorem cyclicRealLpSize_compactMultiplier (P : ℕ) [NeZero P]
    {p : ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K)
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) (H : RealLpMultiplierBound p m K)
    (f : ZMod P → SchwartzMap ℝ ℂ) :
    cyclicRealLpSize P p (fun y x => compactSmoothMultiplier m hs hm (f y) x) ≤
      ENNReal.ofReal K * cyclicRealLpSize P p (fun y x => f y x) :=
  cyclicRealLpSize_mono_bound P p (fun y => (f y).memLp p) hK
    (fun y => compactSmoothMultiplier_Lp m hs hm H (f y))

end PrimeSquares
