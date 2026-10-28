import PrimeSquares.IWPrimeAnnularRestrictedGauge
import PrimeSquares.MangoldtFullAnnularComparison
import PrimeSquares.SectionSevenDeductions

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem iw_prime_full_restricted_gauge {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧ PositiveRestrictedGauge mangoldtPositiveFamily Cg Rg := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_prime_annular_restricted_gauge D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg*(4*Real.exp (4*Cg*Real.log 2))^2, hCg, by positivity, ?_⟩
  exact positiveRestrictedGauge_mangoldt_full hCg hRg.le hG

theorem iw_prime_full_modular_estimates {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧
      (∀ (F : Finset ℤ) (t : ℝ), 1 ≤ t →
        {x | 1/t < positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x}.Finite ∧
        ({x | 1/t < positiveMaximal mangoldtPositiveFamily (finiteIndicator F) x}.ncard : ℝ) ≤
          Rg*(F.card : ℝ)*nearOnePsi Cg t) ∧
      (∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
        ∀ level : ℝ, 0 < level →
        {x | level < positiveMaximal mangoldtPositiveFamily f x}.Finite ∧
        ({x | level < positiveMaximal mangoldtPositiveFamily f x}.ncard : ℝ) ≤
          (Rg*layerGaugeConstant Cg (2*mangoldtPositiveFamily.mass))*
            ∑ x ∈ F.filter (fun x => level/(2*mangoldtPositiveFamily.mass) < ‖f x‖),
              nearOnePsi (9*Cg+4) (‖f x‖/level)) := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_prime_full_restricted_gauge D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg, hCg, hRg, ?_, ?_⟩
  · intro F t ht
    exact (testedDistribution_iff).mp (hG F t ht)
  · intro F f hf level hl
    exact section7_truncated_modular_finite_card mangoldtPositiveFamily hCg hRg.le hG F f hf hl

end PrimeSquares
