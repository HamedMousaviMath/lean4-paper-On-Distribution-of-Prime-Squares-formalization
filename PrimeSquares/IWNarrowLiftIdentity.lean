import PrimeSquares.SchwartzSynthesisMultipliers

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ContDiff ENNReal lp
namespace PrimeSquares

noncomputable def finiteCutoffLift (Γ : Finset ℚ) (P : ℕ) (a : ℝ) (ha : 2 ≤ a)
    (F : Finset ℤ) (f : ℤ → ℂ) (y : ZMod P) : SchwartzMap ℝ ℂ :=
  cyclicSynthesisSchwartz Γ P (finiteLiftComponent (continuousCutoffSymbol a)
    (continuousCutoffSymbol_boundary (by linarith) (by linarith : 1 ≤ a*1))
    (continuousCutoffSymbol_smooth a) F f) y

theorem annularSchwartzOutput_lift (Γ : Finset ℚ) (P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ Γ, α.den ∣ P) (ν : ZMod P → ℂ)
    (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : 2*a ≤ b)
    (F : Finset ℤ) (f : ℤ → ℂ) (y : ZMod P) :
    annularSchwartzOutput N hN β hβ0 hβ1 b hb
      (cyclicConvolutionSchwartz P ν (finiteCutoffLift Γ P a ha F f) y) =
    cyclicConvolutionSchwartz P ν
      (cyclicSynthesisSchwartz Γ P
        (finiteLiftComponent (allAnnularBoundedSymbol N hN β hβ0 hβ1 b)
          (allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1 (by linarith) (by linarith : 1 ≤ b*1))
          (allAnnularBoundedSymbol_smooth N hN β hβ0 hβ1 b) F f)) y := by
  let u := finiteLiftComponent (continuousCutoffSymbol a)
    (continuousCutoffSymbol_boundary (by linarith) (by linarith : 1 ≤ a*1))
    (continuousCutoffSymbol_smooth a) F f
  let v := finiteLiftComponent (allAnnularBoundedSymbol N hN β hβ0 hβ1 b)
    (allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1 (by linarith) (by linarith : 1 ≤ b*1))
    (allAnnularBoundedSymbol_smooth N hN β hβ0 hβ1 b) F f
  change compactSmoothMultiplier _ _ _
    (cyclicConvolutionSchwartz P ν (cyclicSynthesisSchwartz Γ P u) y) =
      cyclicConvolutionSchwartz P ν (cyclicSynthesisSchwartz Γ P v) y
  rw [←cyclicSynthesis_weighted_convolution Γ P hΓ ν u y,
    ←cyclicSynthesis_weighted_convolution Γ P hΓ ν v y]
  apply compactSmoothMultiplier_synthesis
  intro α _ θ
  dsimp only [u, v]
  rw [schwartz_smul_fourier, schwartz_smul_fourier, finiteLiftComponent_fourier, finiteLiftComponent_fourier]
  have hprod := annular_symbol_absorbs_wide_cutoff N hN β hβ0 hβ1 (by linarith : 0 ≤ a)
    (by linarith : 0 < b) hab θ
  calc
    _ = cyclicRationalCoefficient P ν α *
        (allAnnularBoundedSymbol N hN β hβ0 hβ1 b θ * continuousCutoffSymbol a θ) *
        finiteFourierPolynomial F f (((α : ℝ)+θ : ℝ) : PrimeCircle) := by rw [hprod]; ring
    _ = _ := by ring

theorem iw_narrow_lift_diagonal (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (hΓ : ∀ α ∈ iwFrequencySet S k, α.den ∣ P) (ν : ZMod P → ℂ)
    (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : 2*a ≤ b)
    (F : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    annularSchwartzOutput N hN β hβ0 hβ1 b hb
      (cyclicConvolutionSchwartz P ν (finiteCutoffLift (iwFrequencySet S k) P a ha F f)
        (n : ZMod P)) (n : ℝ) =
      iwAnnularLowOperator S k P ν N hN β b hb (finiteInputLp F f 2) n := by
  rw [annularSchwartzOutput_lift (iwFrequencySet S k) P hΓ ν N hN β hβ0 hβ1 ha hb hab]
  have hs := allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1
    (by linarith : 0 ≤ b) (by linarith : 1 ≤ b*1)
  have hn := allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1
    (by linarith : 0 ≤ b) (by linarith : 1 ≤ b*(1/2))
  have h := iw_cyclic_convolution_lift_diagonal S k P hΓ ν
    (allAnnularBoundedSymbol N hN β hβ0 hβ1 b) hs hn
    (allAnnularBoundedSymbol_smooth N hN β hβ0 hβ1 b) F f n
  rw [iwCyclicSymbol_all_annular S k P ν N hN β hβ0 hβ1 b hb hs] at h
  exact h

theorem annularSchwartzOutput_band (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a w : ℝ} (ha : 2 ≤ a)
    (haw : 1 ≤ a*w) (f : SchwartzMap ℝ ℂ) (θ : ℝ) (hθ : w ≤ |θ|) :
    𝓕 (annularSchwartzOutput N hN β hβ0 hβ1 a ha f : ℝ → ℂ) θ = 0 := by
  change 𝓕 (compactSmoothMultiplier _ _ _ f : ℝ → ℂ) θ = 0
  rw [compactSmoothMultiplier_fourier,
    allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1 (by linarith : 0 ≤ a) haw θ hθ, zero_mul]

end PrimeSquares
