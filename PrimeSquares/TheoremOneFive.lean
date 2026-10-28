import PrimeSquares.PersistentBadnessCriterion
import PrimeSquares.TheoremOneFivePartTwo

set_option autoImplicit false
universe u
open MeasureTheory
open scoped ENNReal Topology
namespace PrimeSquares

theorem theorem_1_5_i
    (HW : RawSplitQuadraticWeilInput) (HPNT : RawFixedPrimeProgressionFrequencyInput)
    (HL : RawOriginalLaVictoireInput.{u}) (HSawyer : RawSawyerMaximalInput.{u})
    (HConze : RawConzeMaximalInput.{u}) :
    PersistentUniversalL1Bad.{u} primeSquareSequence :=
  persistent_l1_badness_from_arithmetic HL HSawyer HConze primeSquareSequence
    (primeSquare_lavictoire_arithmetic HW HPNT)

theorem theorem_1_5 {c C Cb E Z R H S : ℝ}
    (HW : RawSplitQuadraticWeilInput) (HPNT : RawFixedPrimeProgressionFrequencyInput)
    (HL : RawOriginalLaVictoireInput.{u}) (HSawyer : RawSawyerMaximalInput.{u})
    (HConze : RawConzeMaximalInput.{u})
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    (HCalderon : RawCalderonStrongInput.{u}) :
    PersistentUniversalL1Bad.{u} primeSquareSequence ∧
  (∃ Cnorm : ℝ, 0 < Cnorm ∧
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
              (eLpNorm f (ENNReal.ofReal p) μ).toReal) := by
  exact ⟨theorem_1_5_i HW HPNT HL HSawyer HConze,
    theorem_1_5_ii D hC hCe hCb HB hE HE hc HP HT hZ hR hH hS HIW HCZ HY HRM
      Hmajor HShannon HHL HRT HCalderon⟩

end PrimeSquares
