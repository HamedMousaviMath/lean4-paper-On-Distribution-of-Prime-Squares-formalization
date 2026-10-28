import PrimeSquares.AEBoundedRealMultipliers
import PrimeSquares.CyclicProductLpOperators
import PrimeSquares.RealIWConstruction
import PrimeSquares.FiniteComplexInputs

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform ENNReal lp
namespace PrimeSquares

/-- A bounded operator on the entire integer Lp space with the literal
finite-convolution kernel. Agreement on finite inputs specifies the
Fourier multiplier independently of a chosen L2 representative. -/
structure FullIntegerKernelMultiplier (K : ℤ → ℂ) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  map : lp (fun _ : ℤ => ℂ) p →L[ℂ] lp (fun _ : ℤ => ℂ) p
  agreement : ∀ (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ),
    map (finiteInputLp F f p) x = finiteConvolution K F f x

noncomputable def cyclicRealFamilyOperator {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (P : ℕ) [NeZero P]
    (A : ZMod P → (Lp ℂ p (volume : Measure ℝ) →L[ℂ] Lp ℂ p (volume : Measure ℝ)))
    (F : ZMod P → Lp ℂ p (volume : Measure ℝ)) (y : ZMod P) :
    Lp ℂ p (volume : Measure ℝ) := ∑ z : ZMod P, A z (F (y-z))

/-- The exact projected inverse kernel of a general finite-arithmetic
adelic multiplier. The spatial cyclic kernels can differ at every z. -/
noncomputable def adelicProjectedKernel (P : ℕ) [NeZero P] (Γ : Finset ℚ)
    (B : ZMod P → ℝ) (m : ∀ z, AEBoundedRealSymbol (B z)) (x : ℤ) : ℂ :=
  ∑ α ∈ Γ, negativeFourierCharacter (-x) ((α : ℝ) : PrimeCircle) *
    ∑ z : ZMod P, negativeFourierCharacter (z.val : ℤ) ((α : ℝ) : PrimeCircle) *
      𝓕⁻ (m z).value (x : ℝ)

/-- The independent full-domain adelic IW theorem in a finite arithmetic
quotient, with arbitrary essentially bounded compact real symbols and
arbitrary spatial cyclic operator kernels. The rough-symbol limiting and
published-to-actual-kernel realization bridges are explicitly part of this
unproved general input. It has no Q, B(Q), chosen construction, probability
measure, annular kernel, maximal estimate or current-paper conclusion. -/
def RawFullAdelicIWInput (C : ℝ) : Prop :=
  ∀ (r k : ℕ), 2 ≤ r → 1 ≤ k → ∀ S : Finset ℕ,
    (∀ s ∈ S, 0 < s) → (S : Set ℕ).Pairwise Nat.Coprime →
    ∀ (P : ℕ) [NeZero P], (∀ α ∈ iwFrequencySet S k, α.den ∣ P) →
    ∀ ε : ℝ, IWGood r k S ε →
    ∀ p : ℝ, iwNearOneExponent r ≤ p → p ≤ 2*(r : ℝ) →
    ∀ [Fact (1 ≤ ENNReal.ofReal p)],
    ∀ B : ZMod P → ℝ, ∀ m : ∀ z, AEBoundedRealSymbol (B z),
      (∀ z, ∀ᵐ θ ∂volume, ε < |θ| → (m z).value θ = 0) →
    ∀ A : ∀ z, FullRealLpMultiplier (m z) (ENNReal.ofReal p),
    ∀ K : ℝ, 0 ≤ K →
      (∀ F : ZMod P → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
        cyclicFamilyLpSize P (ENNReal.ofReal p)
          (cyclicRealFamilyOperator P (fun z => (A z).map) F) ≤
        ENNReal.ofReal K*cyclicFamilyLpSize P (ENNReal.ofReal p) F) →
    ∃ T : FullIntegerKernelMultiplier (adelicProjectedKernel P (iwFrequencySet S k) B m)
        (ENNReal.ofReal p), ‖T.map‖ ≤ iwMultiplierConstant C r k*K

noncomputable def iwRoughKernel {B : ℝ} (P : ℕ) [NeZero P] (Γ : Finset ℚ)
    (ν : ZMod P → ℂ) (m : AEBoundedRealSymbol B) (x : ℤ) : ℂ :=
  ∑ α ∈ Γ, cyclicRationalCoefficient P ν α *
    negativeFourierCharacter (-x) ((α : ℝ) : PrimeCircle)*𝓕⁻ m.value (x : ℝ)

theorem adelicProjectedKernel_rank_one {B : ℝ} (P : ℕ) [NeZero P] (Γ : Finset ℚ)
    (ν : ZMod P → ℂ) (m : AEBoundedRealSymbol B) :
    adelicProjectedKernel P Γ (fun z => ‖ν z‖*B) (fun z => aeRealSymbol_smul (ν z) m) =
      iwRoughKernel P Γ ν m := by
  funext x
  unfold adelicProjectedKernel iwRoughKernel
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [aeRealSymbol_smul_inverse_kernel]
  unfold cyclicRationalCoefficient
  rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem iwRoughKernel_finite_formula {B : ℝ} (P : ℕ) [NeZero P] (Γ : Finset ℚ)
    (ν : ZMod P → ℂ) (m : AEBoundedRealSymbol B)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (iwRoughKernel P Γ ν m) F f x =
      ∑ y ∈ F, (∑ α ∈ Γ, cyclicRationalCoefficient P ν α *
        negativeFourierCharacter (-(x-y)) ((α : ℝ) : PrimeCircle)*
          𝓕⁻ m.value ((x-y : ℤ) : ℝ))*f y := rfl

/-- The entire rough-symbol multiplier clause at the literal real-Q width.
The full real Lp operator is an input because m is assumed to be a real Lp
multiplier; the full integer Lp operator and its norm are conclusions. -/
theorem quantitative_real_iw_full_rough_multiplier {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HIW : RawFullAdelicIWInput C) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    {p : ℝ} (hp0 : iwNearOneExponent r ≤ p) (hp1 : p ≤ 2*(r : ℝ))
    [Fact (1 ≤ ENNReal.ofReal p)] {B : ℝ} (m : AEBoundedRealSymbol B)
    (hε : ∀ᵐ θ ∂volume, realIWWidth C r k Q < |θ| → m.value θ = 0)
    (A : FullRealLpMultiplier m (ENNReal.ofReal p))
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) (hA : ‖A.map‖ ≤ K) :
    ∃ T : FullIntegerKernelMultiplier (iwRoughKernel d.period (iwFrequencySet d.S k) ν m)
        (ENNReal.ofReal p), ‖T.map‖ ≤ iwMultiplierConstant C r k*K := by
  let b : ZMod d.period → ℝ := fun z => ‖ν z‖*B
  let a : ∀ z, AEBoundedRealSymbol (b z) := fun z => aeRealSymbol_smul (ν z) m
  have ha : ∀ z, ∀ᵐ θ ∂volume, realIWWidth C r k Q < |θ| → (a z).value θ = 0 := by
    intro z
    filter_upwards [hε] with θ hθ
    intro hθ'
    change ν z*m.value θ = 0
    rw [hθ hθ',mul_zero]
  have hbound : ∀ F : ZMod d.period → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      cyclicFamilyLpSize d.period (ENNReal.ofReal p)
        (cyclicRealFamilyOperator d.period (fun z => (A.smul (ν z)).map) F) ≤
      ENNReal.ofReal K*cyclicFamilyLpSize d.period (ENNReal.ofReal p) F := by
    intro F
    change cyclicFamilyLpSize d.period (ENNReal.ofReal p)
      (cyclicRealOperator d.period ν A.map F) ≤ _
    exact cyclicRealOperator_TV_one_bound ENNReal.ofReal_ne_top d.period ν hν A.map hK hA F
  have he := adelicProjectedKernel_rank_one d.period (iwFrequencySet d.S k) ν m
  rw [←he]
  exact HIW r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (realIWWidth C r k Q) (real_iw_goodness_from_floor hC hQ hr hk d) p hp0 hp1
      b a ha (fun z => A.smul (ν z)) K hK hbound

theorem source_iw_rough_multiplier_norm {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HIW : RawFullAdelicIWInput C) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    {p : ℝ} (hp0 : iwNearOneExponent r ≤ p) (hp1 : p ≤ 2*(r : ℝ))
    [Fact (1 ≤ ENNReal.ofReal p)] {B : ℝ} (m : AEBoundedRealSymbol B)
    (hε : ∀ᵐ θ ∂volume, realIWWidth C r k Q < |θ| → m.value θ = 0)
    (A : FullRealLpMultiplier m (ENNReal.ofReal p))
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1) :
    ∃ T : FullIntegerKernelMultiplier (iwRoughKernel d.period (iwFrequencySet d.S k) ν m)
        (ENNReal.ofReal p), ‖T.map‖ ≤ iwMultiplierConstant C r k*‖A.map‖ :=
  quantitative_real_iw_full_rough_multiplier hC hQ HIW hr hk d hp0 hp1 m hε A ν hν
    (norm_nonneg A.map) le_rfl

end PrimeSquares
