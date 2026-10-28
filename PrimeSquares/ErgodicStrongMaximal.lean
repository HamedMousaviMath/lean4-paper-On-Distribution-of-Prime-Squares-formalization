import PrimeSquares.ErgodicIndependentInputs

set_option autoImplicit false
universe u
open MeasureTheory
open scoped ENNReal Topology
namespace PrimeSquares

theorem ergodic_strong_maximal_source {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    (HCalderon : RawCalderonStrongInput.{u}) :
    ∃ Cnorm : ℝ, 0 < Cnorm ∧ ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
      ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (T : X ≃ᵐ X), MeasurePreserving T μ μ →
        ∀ f : X → ℂ, MemLp f (ENNReal.ofReal p) μ →
          (∀ᵐ x ∂μ, ergodicMaximalENorm A T f x < ∞) ∧
          MemLp (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ∧
          eLpNorm (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal (Real.exp (Cnorm/(p-1)*Real.log (Real.exp 1/(p-1))))*
              eLpNorm f (ENNReal.ofReal p) μ := by
  obtain ⟨Cnorm, hCnorm, hDiscrete⟩ := corollary_7_6 D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cnorm, hCnorm, ?_⟩
  intro A hA p hp hp2 X _ μ _ T hT f hf
  exact calderon_strong_apply HCalderon A hp (Real.exp_pos _).le (hDiscrete A hA p hp hp2) μ T hT hf

end PrimeSquares
