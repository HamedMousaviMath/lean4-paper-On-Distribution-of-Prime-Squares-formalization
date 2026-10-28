import PrimeSquares.IWFiniteLiftIdentity
import PrimeSquares.AnnularFourierSmoothness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ContDiff lp
namespace PrimeSquares

theorem compact_support_of_unit_boundary {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, 1 ≤ |x| → f x = 0) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))
  intro x hx
  have ha : |x| < 1 := by
    by_contra h
    exact hx (hf x (le_of_not_gt h))
  exact ⟨by linarith [(abs_lt.mp ha).1], by linarith [(abs_lt.mp ha).2]⟩

theorem finiteFourierPolynomial_shift_smooth (F : Finset ℤ) (f : ℤ → ℂ) (α : ℝ) :
    ContDiff ℝ ∞ (fun θ : ℝ => finiteFourierPolynomial F f ((α+θ : ℝ) : PrimeCircle)) := by
  have he : (fun θ : ℝ => finiteFourierPolynomial F f ((α+θ : ℝ) : PrimeCircle)) =
      fun θ : ℝ => ∑ n ∈ F, f n * Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*((α+θ : ℝ) : ℂ))) := by
    funext θ
    exact finiteFourierPolynomial_real F f (α+θ)
  rw [he]
  apply ContDiff.sum
  intro n _
  have hc : ContDiff ℝ ∞ (fun θ : ℝ => ((α+θ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.add contDiff_id)
  exact contDiff_const.mul ((contDiff_const.mul hc).neg.cexp)

noncomputable def finiteLiftFrequencyMap (m : BoundedContinuousFunction ℝ ℂ)
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) : C(ℝ, ℂ) :=
  ⟨fun θ => m θ * finiteFourierPolynomial F f (((α : ℝ)+θ : ℝ) : PrimeCircle),
    m.continuous.mul ((finiteFourierPolynomial F f).continuous.comp
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.add continuous_id)))⟩

theorem finiteLiftFrequencyMap_boundary (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) (θ : ℝ) (hθ : 1 ≤ |θ|) :
    finiteLiftFrequencyMap m F f α θ = 0 := by
  change m θ * _ = 0
  rw [hs θ hθ, zero_mul]

theorem finiteLiftFrequencyMap_smooth (m : BoundedContinuousFunction ℝ ℂ)
    (hm : ContDiff ℝ ∞ (m : ℝ → ℂ)) (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) :
    ContDiff ℝ ∞ (finiteLiftFrequencyMap m F f α : ℝ → ℂ) :=
  hm.mul (finiteFourierPolynomial_shift_smooth F f (α : ℝ))

noncomputable def finiteLiftFrequencySchwartz (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) : SchwartzMap ℝ ℂ :=
  (compact_support_of_unit_boundary (finiteLiftFrequencyMap_boundary m hs F f α)).toSchwartzMap
    (finiteLiftFrequencyMap_smooth m hm F f α)

noncomputable def finiteLiftComponent (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (finiteLiftFrequencySchwartz m hs hm F f α)

theorem finiteLiftFrequencySchwartz_apply (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) (θ : ℝ) :
    finiteLiftFrequencySchwartz m hs hm F f α θ =
      m θ * finiteFourierPolynomial F f (((α : ℝ)+θ : ℝ) : PrimeCircle) := rfl

theorem finiteLiftComponent_fourier (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) (θ : ℝ) :
    𝓕 (finiteLiftComponent m hs hm F f α : ℝ → ℂ) θ =
      m θ * finiteFourierPolynomial F f (((α : ℝ)+θ : ℝ) : PrimeCircle) := by
  have hF : (𝓕 (𝓕⁻ (finiteLiftFrequencySchwartz m hs hm F f α) : SchwartzMap ℝ ℂ) :
      SchwartzMap ℝ ℂ) = finiteLiftFrequencySchwartz m hs hm F f α :=
    FourierTransform.fourier_fourierInv_eq _
  have he := congrArg (fun v : SchwartzMap ℝ ℂ => v θ) hF
  simpa only [finiteLiftComponent, SchwartzMap.fourier_coe, finiteLiftFrequencySchwartz_apply] using he

theorem finiteLiftFrequency_periodization (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) :
    compactCircleLift (finiteLiftFrequencyMap m F f α) (finiteLiftFrequencyMap_boundary m hs F f α) =
      compactCircleLift m.toContinuousMap hs *
        (finiteFourierPolynomial F f).comp
          ⟨fun ξ => ((α : ℝ) : PrimeCircle)+ξ, by fun_prop⟩ := by
  apply compactCircleLift_mul_circle
  intro θ
  change m θ * finiteFourierPolynomial F f (((α : ℝ)+θ : ℝ) : PrimeCircle) = _
  rw [AddCircle.coe_add]
  rfl

theorem finiteLiftFrequency_shift_periodization (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) :
    circleSymbolTranslate
      (compactCircleLift (finiteLiftFrequencyMap m F f α) (finiteLiftFrequencyMap_boundary m hs F f α))
      ((α : ℝ) : PrimeCircle) =
    circleSymbolTranslate (compactCircleLift m.toContinuousMap hs) ((α : ℝ) : PrimeCircle) *
      finiteFourierPolynomial F f := by
  rw [finiteLiftFrequency_periodization]
  ext ξ
  change compactCircleLift m.toContinuousMap hs (ξ-((α : ℝ) : PrimeCircle)) *
    finiteFourierPolynomial F f (((α : ℝ) : PrimeCircle)+(ξ-((α : ℝ) : PrimeCircle))) = _
  have he : ((α : ℝ) : PrimeCircle)+(ξ-((α : ℝ) : PrimeCircle)) = ξ := by abel
  rw [he]
  rfl

theorem finiteLiftComponent_inverse (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (α : ℚ) (x : ℝ) :
    finiteLiftComponent m hs hm F f α x = 𝓕⁻ (finiteLiftFrequencyMap m F f α : ℝ → ℂ) x := by
  change (𝓕⁻ (finiteLiftFrequencySchwartz m hs hm F f α) : SchwartzMap ℝ ℂ) x = _
  rw [SchwartzMap.fourierInv_coe]
  rfl

theorem finite_arc_projection_formula (Γ : Finset ℚ) (c : ℚ → ℂ)
    (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    integerMultiplier (∑ α ∈ Γ, c α •
      circleSymbolTranslate (compactCircleLift m.toContinuousMap hs) ((α : ℝ) : PrimeCircle))
      (finiteInputLp F f 2) n =
      ∑ α ∈ Γ, c α * negativeFourierCharacter (-n) ((α : ℝ) : PrimeCircle) *
        finiteLiftComponent m hs hm F f α (n : ℝ) := by
  rw [integerMultiplier_finite_symbol_product, Finset.sum_mul, fourierKernel_finsetSum]
  apply Finset.sum_congr rfl
  intro α _
  rw [smul_mul_assoc, fourierKernel_smul,
    ←finiteLiftFrequency_shift_periodization m hs F f α, fourierKernel_translate]
  have hhalf : ∀ θ : ℝ, 1/2 ≤ |θ| → finiteLiftFrequencyMap m F f α θ = 0 := by
    intro θ hθ
    change m θ * _ = 0
    rw [hn θ hθ, zero_mul]
  rw [compactCircleLift_inverse_kernel _ (finiteLiftFrequencyMap_boundary m hs F f α) hhalf,
    ←finiteLiftComponent_inverse m hs hm F f α]
  ring

theorem iwCyclicSymbol_finite_lift (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hs : ∀ θ : ℝ, 1 ≤ |θ| → m θ = 0)
    (hn : ∀ θ : ℝ, 1/2 ≤ |θ| → m θ = 0) (hm : ContDiff ℝ ∞ (m : ℝ → ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    integerMultiplier (iwCyclicSymbol S k P ν m hs) (finiteInputLp F f 2) n =
      ∑ α ∈ iwFrequencySet S k, cyclicRationalCoefficient P ν α *
        negativeFourierCharacter (-n) ((α : ℝ) : PrimeCircle) *
        finiteLiftComponent m hs hm F f α (n : ℝ) :=
  finite_arc_projection_formula (iwFrequencySet S k) _ m hs hn hm F f n

end PrimeSquares
