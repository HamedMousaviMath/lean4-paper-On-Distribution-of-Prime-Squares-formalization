import PrimeSquares.IWFullSquareAnnularRestrictedGauge
import PrimeSquares.OrdinaryFullAnnularComparison
import PrimeSquares.SectionSevenDeductions

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem iw_full_square_restricted_gauge {C Cb E Z R H S : ℝ}
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧ PositiveRestrictedGauge ordinaryPositiveFamily Cg Rg := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_full_square_annular_restricted_gauge hC hCe hCb HB hE HE HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg*(4*Real.exp (4*Cg*Real.log 2))^2, hCg, by positivity, ?_⟩
  exact positiveRestrictedGauge_ordinary_full hCg hRg.le hG

theorem iw_full_square_modular_estimates {C Cb E Z R H S : ℝ}
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧
      (∀ (F : Finset ℤ) (t : ℝ), 1 ≤ t →
        {x | 1/t < positiveMaximal ordinaryPositiveFamily (finiteIndicator F) x}.Finite ∧
        ({x | 1/t < positiveMaximal ordinaryPositiveFamily (finiteIndicator F) x}.ncard : ℝ) ≤
          Rg*(F.card : ℝ)*nearOnePsi Cg t) ∧
      (∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
        ∀ level : ℝ, 0 < level →
        {x | level < positiveMaximal ordinaryPositiveFamily f x}.Finite ∧
        ({x | level < positiveMaximal ordinaryPositiveFamily f x}.ncard : ℝ) ≤
          (Rg*layerGaugeConstant Cg (2*ordinaryPositiveFamily.mass))*
            ∑ x ∈ F.filter (fun x => level/(2*ordinaryPositiveFamily.mass) < ‖f x‖),
              nearOnePsi (9*Cg+4) (‖f x‖/level)) := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_full_square_restricted_gauge hC hCe hCb HB hE HE HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg, hCg, hRg, ?_, ?_⟩
  · intro F t ht
    exact (testedDistribution_iff).mp (hG F t ht)
  · intro F f hf level hl
    exact section7_truncated_modular_finite_card ordinaryPositiveFamily hCg hRg.le hG F f hf hl

end PrimeSquares
