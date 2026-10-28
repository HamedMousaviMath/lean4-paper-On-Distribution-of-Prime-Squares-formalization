import PrimeSquares.FiniteSignedMaximalProof
import PrimeSquares.CorollarySevenFortySix
import PrimeSquares.TheoremOneFive

set_option autoImplicit false
universe u
open MeasureTheory
open scoped ENNReal Topology lp
namespace PrimeSquares

/-- Source conclusion with the finite signed maximal input discharged by its proved constant. -/
theorem theorem_7_2_closed_signed_maximal {c C Cb E Z H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg C₀ K : ℝ, 1 ≤ Cg ∧ 1 ≤ C₀ ∧ 1 ≤ K ∧ SectionSevenOrliczConclusion Cg C₀ K := by
  exact theorem_7_2 D hC hCe hCb HB hE HE hc HP HT hZ (by norm_num) hH hS HIW HCZ HY
    rawFiniteSignedMaximalInput_proved Hmajor HShannon HHL HRT

/-- Source conclusion with the finite signed maximal input discharged by its proved constant. -/
theorem corollary_7_6_closed_signed_maximal {c C Cb E Z H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cnorm : ℝ, 0 < Cnorm ∧ ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
      PositiveStrongMaximalBound A p (Real.exp (Cnorm/(p-1)*Real.log (Real.exp 1/(p-1)))) := by
  exact corollary_7_6 D hC hCe hCb HB hE HE hc HP HT hZ (by norm_num) hH hS HIW HCZ HY
    rawFiniteSignedMaximalInput_proved Hmajor HShannon HHL HRT

/-- Source conclusion with the finite signed maximal input discharged by its proved constant. -/
theorem corollary_7_46_closed_signed_maximal {c C Cb E Z H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    (HStrong : RawCalderonStrongInput.{u}) (HModular : RawCalderonModularInput.{u})
    (HBounded : RawBoundedSquarePointwiseInput.{u}) :
    ∃ Cfinal Kfinal : ℝ, 1 ≤ Cfinal ∧ 1 ≤ Kfinal ∧ ErgodicOrliczConclusion.{u} Cfinal Kfinal := by
  exact corollary_7_46 D hC hCe hCb HB hE HE hc HP HT hZ (by norm_num) hH hS HIW HCZ HY
    rawFiniteSignedMaximalInput_proved Hmajor HShannon HHL HRT HStrong HModular HBounded

/-- Source conclusion with the finite signed maximal input discharged by its proved constant. -/
theorem theorem_1_5_ii_closed_signed_maximal {c C Cb E Z H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (Hmajor : RawMajorArcSamplingInput C)
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
  exact theorem_1_5_ii D hC hCe hCb HB hE HE hc HP HT hZ (by norm_num) hH hS HIW HCZ HY
    rawFiniteSignedMaximalInput_proved Hmajor HShannon HHL HRT HCalderon

end PrimeSquares
