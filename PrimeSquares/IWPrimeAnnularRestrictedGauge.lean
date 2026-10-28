import PrimeSquares.IWPrimeRestrictedDistribution
import PrimeSquares.IWOptimizedDistributionBudget
import PrimeSquares.RestrictedToModular

set_option autoImplicit false
open MeasureTheory Finset
namespace PrimeSquares

theorem iw_prime_annular_restricted_gauge {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cg Rg : ℝ, 0 ≤ Cg ∧ 0 < Rg ∧ PositiveRestrictedGauge mangoldtAnnularDyadicFamily Cg Rg := by
  obtain ⟨Cstart, KH, hstart, hKH, hdist⟩ := iw_prime_annular_restricted_distribution D hC hCe hCb HB hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  let K := iwCompleteLowConstant Z R H S
  let Cg := iwRestrictedGaugeRate C
  let R0 := iwRestrictedBudgetConstant C Cstart K KH primeSquareChebyshevConstant
  let Rg := R0*(2*Real.exp (2*Cg*Real.log 2))
  have hK : 0 ≤ K := (iwCompleteLowConstant_pos hZ hR hH hS).le
  have hm : 0 ≤ primeSquareChebyshevConstant := zero_le_one.trans mangoldtPositiveFamily.mass_one_le
  obtain ⟨hCg, hR0⟩ := iwRestrictedBudget_constants (KH:=KH) hC hstart hK hm
  refine ⟨Cg, Rg, hCg, by dsimp [Rg]; positivity, ?_⟩
  intro F t ht E
  let v := nearOneLog t
  let r := iwRestrictedOrder v
  let k := iwBalancedRank v
  let Q := iwRestrictedCutoff v
  let J := iwRestrictedStartingIndex C Cstart v
  have hv : 1 ≤ v := nearOneLog_one_le t
  have hr : 2 ≤ r := (iwRestrictedOrder_bounds hv).1
  have hk : 4 ≤ k := (iwRestrictedRank_bounds hv).1
  have hQ : 2^k ≤ Q := (iwRestrictedCutoff_bounds hv).1
  have hJ := iwRestrictedStartingIndex_admissible C Cstart v
  have hd := hdist r k Q J hr hk hQ hJ.1 hJ.2 F t (by linarith)
  have hb := mul_le_mul_of_nonneg_right (iwRestrictedDistribution_budget (KH:=KH) hC hstart hK hm ht)
    (Nat.cast_nonneg F.card : (0 : ℝ) ≤ F.card)
  have hpsi := mul_le_mul_of_nonneg_left (nearOnePsi_comparison hCg (show 0 ≤ t by linarith))
    (mul_nonneg hR0.le (Nat.cast_nonneg F.card))
  calc
    _ ≤ t*(J : ℝ)*primeSquareChebyshevConstant*(F.card : ℝ)+
        (2*t)^(iwNearOneExponent r)*((2*K*iwMaximalCost C r k Q)^(iwNearOneExponent r)*(F.card : ℝ))+
        4*t^2*(KH^2*(Q : ℝ)^(-(1/2 : ℝ))*(F.card : ℝ)) := hd E
    _ = (t*(J : ℝ)*primeSquareChebyshevConstant+
        (2*t)^(iwNearOneExponent r)*(2*K*iwMaximalCost C r k Q)^(iwNearOneExponent r)+
        4*t^2*(KH^2*(Q : ℝ)^(-(1/2 : ℝ))))*(F.card : ℝ) := by ring
    _ ≤ R0*t*Real.exp (Cg*nearOneCore v)*(F.card : ℝ) := hb
    _ = R0*(F.card : ℝ)*(t*nearOneDensity Cg t) := by
      change R0*t*Real.exp (Cg*nearOneCore (nearOneLog t))*(F.card : ℝ) =
        R0*(F.card : ℝ)*(t*Real.exp (Cg*nearOneCore (nearOneLog t)))
      ring
    _ ≤ R0*(F.card : ℝ)*((2*Real.exp (2*Cg*Real.log 2))*nearOnePsi Cg t) := hpsi
    _ = Rg*(F.card : ℝ)*nearOnePsi Cg t := by dsimp [Rg]; ring

end PrimeSquares
