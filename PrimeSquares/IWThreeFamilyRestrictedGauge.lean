import PrimeSquares.IWFullSquareRestrictedGauge
import PrimeSquares.IWUnweightedPrimeRestrictedGauge

set_option autoImplicit false
open Finset
namespace PrimeSquares

def IsSectionSevenFamily (A : PositiveAverageFamily) : Prop :=
  A = mangoldtPositiveFamily ∨ A = ordinaryPositiveFamily ∨ A = primePositiveFamily

theorem iw_three_families_restricted_gauges {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 1 ≤ Cg ∧ 1 ≤ Rg ∧
      ∀ A : PositiveAverageFamily, IsSectionSevenFamily A → PositiveRestrictedGauge A Cg Rg := by
  obtain ⟨Cp, Rp, hCp, hRp, hMangoldt, hPrime⟩ := iw_prime_families_restricted_gauges D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  obtain ⟨Co, Ro, hCo, hRo, hOrdinary⟩ := iw_full_square_restricted_gauge hC hCe hCb HB hE HE HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  let Cg := max Cp Co+1
  let Rg := Rp+Ro+1
  have hpg : Cp ≤ Cg := by dsimp [Cg]; linarith [le_max_left Cp Co]
  have hog : Co ≤ Cg := by dsimp [Cg]; linarith [le_max_right Cp Co]
  have hpr : Rp ≤ Rg := by dsimp [Rg]; linarith
  have hor : Ro ≤ Rg := by dsimp [Rg]; linarith
  refine ⟨Cg, Rg, by linarith, by dsimp [Rg]; linarith, ?_⟩
  intro A hA
  rcases hA with rfl | rfl | rfl
  · exact positiveRestrictedGauge_enlarge mangoldtPositiveFamily hpg hpr (by linarith) hMangoldt
  · exact positiveRestrictedGauge_enlarge ordinaryPositiveFamily hog hor hRo.le hOrdinary
  · exact positiveRestrictedGauge_enlarge primePositiveFamily hpg hpr (by linarith) hPrime

end PrimeSquares
