import PrimeSquares.PrimeErgodicEnumeration
import PrimeSquares.ErgodicStrongMaximal

set_option autoImplicit false
universe u
open MeasureTheory
open scoped ENNReal Topology
namespace PrimeSquares

theorem theorem_1_5_ii {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    (HCalderon : RawCalderonStrongInput.{u}) :
    ∃ Cnorm : ℝ, 0 < Cnorm ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (T : X ≃ᵐ X), MeasurePreserving T μ μ → ∀ p : ℝ, 1 < p → p ≤ 2 →
        ∀ f : X → ℂ, MemLp f (ENNReal.ofReal p) μ →
          (∀ᵐ x ∂μ, enumeratedPrimeMaximalENorm T f x < ∞) ∧
          MemLp (enumeratedPrimeMaximalValue T f) (ENNReal.ofReal p) μ ∧
          eLpNorm (enumeratedPrimeMaximalValue T f) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal (Real.exp (Cnorm/(p-1)*Real.log (Real.exp 1/(p-1))))*
              eLpNorm f (ENNReal.ofReal p) μ ∧
          (eLpNorm (enumeratedPrimeMaximalValue T f) (ENNReal.ofReal p) μ).toReal ≤
            Real.exp (Cnorm/(p-1)*Real.log (Real.exp 1/(p-1)))*
              (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  obtain ⟨Cnorm, hCnorm, hStrong⟩ := ergodic_strong_maximal_source D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT HCalderon
  refine ⟨Cnorm, hCnorm, ?_⟩
  intro X _ μ _ T hT p hp hp2 f hf
  obtain ⟨hfinite, hmem, hnorm⟩ := hStrong primePositiveFamily (Or.inr (Or.inr rfl)) p hp hp2 X μ T hT f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [enumeratedPrimeMaximalENorm_eq] using hfinite
  · rw [enumeratedPrimeMaximalValue_eq]
    exact hmem
  · rw [enumeratedPrimeMaximalValue_eq]
    exact hnorm
  · rw [enumeratedPrimeMaximalValue_eq]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) hnorm
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

end PrimeSquares
