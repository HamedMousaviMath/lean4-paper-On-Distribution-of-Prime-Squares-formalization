import PrimeSquares.IWPrimeFullRestrictedGauge
import PrimeSquares.PrimeMangoldtMaximalComparison

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem nearOnePsi_mono_coefficient {C D t : ℝ} (hCD : C ≤ D) (ht : 0 ≤ t) :
    nearOnePsi C t ≤ nearOnePsi D t := by
  apply intervalIntegral.integral_mono_on ht
    ((nearOneDensity_continuous C).intervalIntegrable 0 t)
    ((nearOneDensity_continuous D).intervalIntegrable 0 t)
  intro u _hu
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCD (nearOneRate_nonneg u))

theorem positiveRestrictedGauge_enlarge (A : PositiveAverageFamily) {C D R T : ℝ}
    (hCD : C ≤ D) (hRT : R ≤ T) (hR : 0 ≤ R) (H : PositiveRestrictedGauge A C R) :
    PositiveRestrictedGauge A D T := by
  intro F t ht E
  have ht0 : 0 ≤ t := by linarith
  calc
    _ ≤ R*(F.card : ℝ)*nearOnePsi C t := H F t ht E
    _ ≤ R*(F.card : ℝ)*nearOnePsi D t := mul_le_mul_of_nonneg_left
      (nearOnePsi_mono_coefficient hCD ht0) (mul_nonneg hR (Nat.cast_nonneg F.card))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRT (Nat.cast_nonneg F.card))
      (nearOnePsi_nonneg D ht0)

theorem iw_unweighted_prime_restricted_gauge {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧ PositiveRestrictedGauge primePositiveFamily Cg Rg := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_prime_full_restricted_gauge D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg*(3072*Real.exp (2*Cg*Real.log 3072)*(2*Real.exp (2*Cg*Real.log 2))), hCg, by positivity, ?_⟩
  exact positiveRestrictedGauge_mangoldt_to_prime hCg hRg.le hG

theorem iw_unweighted_prime_modular_estimates {c C Cb Z R H S : ℝ}
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
        {x | 1/t < positiveMaximal primePositiveFamily (finiteIndicator F) x}.Finite ∧
        ({x | 1/t < positiveMaximal primePositiveFamily (finiteIndicator F) x}.ncard : ℝ) ≤
          Rg*(F.card : ℝ)*nearOnePsi Cg t) ∧
      (∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
        ∀ level : ℝ, 0 < level →
        {x | level < positiveMaximal primePositiveFamily f x}.Finite ∧
        ({x | level < positiveMaximal primePositiveFamily f x}.ncard : ℝ) ≤
          (Rg*layerGaugeConstant Cg (2*primePositiveFamily.mass))*
            ∑ x ∈ F.filter (fun x => level/(2*primePositiveFamily.mass) < ‖f x‖),
              nearOnePsi (9*Cg+4) (‖f x‖/level)) := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_unweighted_prime_restricted_gauge D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  refine ⟨Cg, Rg, hCg, hRg, ?_, ?_⟩
  · intro F t ht
    exact (testedDistribution_iff).mp (hG F t ht)
  · intro F f hf level hl
    exact section7_truncated_modular_finite_card primePositiveFamily hCg hRg.le hG F f hf hl

theorem iw_prime_families_restricted_gauges {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 1 ≤ Cg ∧ 1 ≤ Rg ∧
      PositiveRestrictedGauge mangoldtPositiveFamily Cg Rg ∧
      PositiveRestrictedGauge primePositiveFamily Cg Rg := by
  obtain ⟨Cg, Rg, hCg, hRg, hG⟩ := iw_prime_full_restricted_gauge D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  let Rp := Rg*(3072*Real.exp (2*Cg*Real.log 3072)*(2*Real.exp (2*Cg*Real.log 2)))
  have hRp : 0 < Rp := by dsimp [Rp]; positivity
  have hPrime : PositiveRestrictedGauge primePositiveFamily Cg Rp :=
    positiveRestrictedGauge_mangoldt_to_prime hCg hRg.le hG
  refine ⟨Cg+1, Rg+Rp+1, by linarith, by linarith, ?_, ?_⟩
  · exact positiveRestrictedGauge_enlarge mangoldtPositiveFamily (by linarith) (by linarith) hRg.le hG
  · exact positiveRestrictedGauge_enlarge primePositiveFamily (by linarith) (by linarith) hRp.le hPrime

end PrimeSquares
