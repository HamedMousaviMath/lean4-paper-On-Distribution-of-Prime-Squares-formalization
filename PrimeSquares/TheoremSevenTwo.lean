import PrimeSquares.SectionSevenThreeFamilyAssembly

set_option autoImplicit false
namespace PrimeSquares

theorem theorem_7_2 {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg C₀ K : ℝ, 1 ≤ Cg ∧ 1 ≤ C₀ ∧ 1 ≤ K ∧ SectionSevenOrliczConclusion Cg C₀ K := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_three_families_restricted_gauges D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  exact section7_three_family_assembly hCg hRg hG

end PrimeSquares
