import PrimeSquares.IWPrimeLowMaximum
import PrimeSquares.FiniteInputMaximalExtension

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

theorem iwNearOneExponent_toReal_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < (ENNReal.ofReal (iwNearOneExponent r)).toReal := by
  rw [ENNReal.toReal_ofReal (by linarith [(iwNearOneExponent_bounds hr).1] : 0 ≤ iwNearOneExponent r)]
  linarith [(iwNearOneExponent_bounds hr).1]

theorem iwNearOneExponent_ennreal_le_two {r : ℕ} (hr : 2 ≤ r) :
    ENNReal.ofReal (iwNearOneExponent r) ≤ 2 := by
  have h := ENNReal.ofReal_le_ofReal (show iwNearOneExponent r ≤ 2 by linarith [(iwNearOneExponent_bounds hr).2])
  simpa only [ENNReal.ofReal_ofNat] using h

theorem iw_full_low_maximal_bound {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha : 2 ≤ iwCutoffScale C r k Q) :
    AllInputLpMaximalBound (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha)
      (ENNReal.ofReal (iwNearOneExponent r)) (iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q) := by
  apply finite_input_maximal_extension _ (iwNearOneExponent_toReal_pos hr)
  intro F f
  exact iw_finite_input_low_majorant hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d ν hν hβ0 hβ1 F f (finiteInputLp_count_memLp F f (iwNearOneExponent_toReal_pos hr)) ha

theorem iw_prime_low_maximal_bound {c C Z R H S : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (E₀ : Option PageZeroDatum) (hsmall : ∀ E, E₀ = some E → E.conductor ≤ Q)
    (ha : 2 ≤ iwCutoffScale C r k Q) :
    AllInputLpMaximalBound (fun j => iwPrimeLowOperator D (iwFrequencySet d.S k) ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) (iwCutoffScale C r k Q) ha E₀ Q)
      (ENNReal.ofReal (iwNearOneExponent r)) (2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q) := by
  apply finite_input_maximal_extension _ (iwNearOneExponent_toReal_pos hr)
  intro F f
  exact iw_prime_finite_low_majorant D hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d E₀ hsmall F f ha

theorem iw_low_all_integer_lp {C Z R H S : ℝ} (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : 1 ≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha : 2 ≤ iwCutoffScale C r k Q)
    (f : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℂ)) :
    ∃ G : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℝ), (∀ x, 0 ≤ G x) ∧
      (∀ j x, ‖iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β
        (iwCutoffScale C r k Q) ha
        (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) (iwNearOneExponent_ennreal_le_two hr) f) x‖ ≤ G x) ∧
      ‖G‖ ≤ iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q*‖f‖ := by
  have hbound := iw_full_low_maximal_bound hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ d ν hν hβ0 hβ1 ha
  have hK : 0 ≤ iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q :=
    mul_nonneg (iwCompleteLowConstant_pos hZ hR hH hS).le
      ((by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans (iwMaximalCost_lower_bounds hC hr k Q).1)
  exact allInputLpMaximalBound_integerLp _ (iwNearOneExponent_toReal_pos hr)
    (iwNearOneExponent_ennreal_le_two hr) hK hbound f

end PrimeSquares
