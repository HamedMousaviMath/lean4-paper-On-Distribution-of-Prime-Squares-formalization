import PrimeSquares.IWFullSquareHighSourceScale
import PrimeSquares.OrdinaryAnnularPositiveFamily
import PrimeSquares.IWPrimeRestrictedDistribution

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal lp
namespace PrimeSquares

theorem iwFullSquareHighOperator_scale_congr (S : Finset ℕ) (k P : ℕ) [NeZero P]
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (he : N = M) (a : ℝ) (ha : 2 ≤ a) :
    iwFullSquareHighOperator S k P N hN a ha = iwFullSquareHighOperator S k P M hM a ha := by
  cases he
  rfl

theorem iw_full_square_annular_restricted_distribution {C Cb E Z R H S : ℝ}
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput) :
    ∃ Cstart KH : ℝ, 0 < Cstart ∧ 0 < KH ∧
      ∀ (r k Q J : ℕ), 2 ≤ r → 4 ≤ k → 2^k ≤ Q → 1 ≤ J →
      Real.exp (Cstart*((Real.log (Q : ℝ))^2+
        (r : ℝ)*Real.log (iwDenominatorBound C k Q))) ≤ (((2 : ℕ)^J : ℕ) : ℝ) →
      ∀ (F : Finset ℤ) (t : ℝ), 0 < t →
      TestedDistributionBound (positiveMaximal ordinaryAnnularDyadicFamily (finiteIndicator F)) (1/t)
        (t*(J : ℝ)*primeSquareChebyshevConstant*(F.card : ℝ)+
          (2*t)^(iwNearOneExponent r)*
            ((2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)^(iwNearOneExponent r)*(F.card : ℝ))+
          4*t^2*(KH^2*(Q : ℝ)^(-(1/2 : ℝ))*(F.card : ℝ))) := by
  obtain ⟨Cstart, KH, hstart0, hKH, hHigh⟩ := iw_full_square_high_source_scale hCb HB hE HE
  refine ⟨Cstart, KH, hstart0, hKH, ?_⟩
  intro r k Q J hr hk hQ hJ hstart F t ht
  have hQ1 : 1 ≤ Q := (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))).trans hQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hM : 2 ≤ (2 : ℕ)^J := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hJ
  have hEven : Even ((2 : ℕ)^J) := by
    exact (show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)
  obtain ⟨d, _hgood, _hden, hHi⟩ := hHigh C hC hCe HT r k Q ((2 : ℕ)^J) hr hk hQ hM hEven hstart
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  have ha : 2 ≤ iwCutoffScale C r k Q := by have h := iwCutoffScale_four_le hC hr k Q; linarith
  have hpR := iwNearOneExponent_toReal_pos hr
  have hp : 0 < iwNearOneExponent r := lt_trans zero_lt_one (iwNearOneExponent_bounds hr).1
  have hp0 : 0 ≤ iwNearOneExponent r := hp.le
  have hf := finiteInputLp_count_memLp F (fun _ => (1 : ℂ)) hpR
  rw [finiteInputLp_one] at hf
  have hLow := iw_full_square_low_maximal_bound hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ1 d ha
  obtain ⟨gLo, hGL0, hGLm, hGLdom, hGLnorm⟩ := hLow (finiteIndicatorLp F 2) hf
  have hGLnorm' : eLpNorm gLo (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
      ENNReal.ofReal (2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)*
        eLpNorm (finiteIndicatorLp F 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
    apply hGLnorm.trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    have hc0 := (iwCompleteLowConstant_pos hZ hR hH hS).le
    have hd0 : 0 ≤ iwMaximalCost C r k Q :=
      ((by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans (iwMaximalCost_lower_bounds hC hr k Q).1)
    nlinarith
  obtain ⟨gHi, hGH0, hGHdom, hGHnorm⟩ := hHi (finiteIndicatorLp F 2)
  have hKlow : 0 ≤ 2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q :=
    mul_nonneg (mul_nonneg (by norm_num) (iwCompleteLowConstant_pos hZ hR hH hS).le)
      ((by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans (iwMaximalCost_lower_bounds hC hr k Q).1)
  have hLoBudget : FinitePowerBudget gLo (iwNearOneExponent r)
      ((2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)^(iwNearOneExponent r)*(F.card : ℝ)) := by
    simpa only [ENNReal.toReal_ofReal hp0] using
      count_Lp_indicator_power_budget hpR hGLm hGL0 F hKlow hGLnorm'
  have hHiBudget := primeHigh_indicator_power_budget hQR F gHi hGH0 hGHnorm
  have hlarge : ∀ n : ℕ, J ≤ n → ∀ x,
      ‖positiveAverage ordinaryAnnularDyadicFamily n (finiteIndicator F) x‖ ≤ gLo x+gHi x := by
    intro n hn x
    have hscale : (2 : ℕ)^(n-J)*(2 : ℕ)^J = (2 : ℕ)^n := by
      rw [←pow_add, Nat.sub_add_cancel hn]
    have hprod : 1 ≤ (2 : ℕ)^(n-J)*(2 : ℕ)^J := by
      have hs := dyadic_annular_scale_lower hM (n-J)
      omega
    have hhi := hGHdom (n-J) x
    rw [iwFullSquareHighOperator_scale_congr d.S k d.period hprod
      (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hscale (iwCutoffScale C r k Q) ha] at hhi
    have hlo := hGLdom n x
    change ‖positiveAverage ordinaryAnnularDyadicFamily n (finiteIndicatorLp F 2 : ℤ → ℂ) x‖ ≤ _
    rw [ordinaryAnnularDyadicFamily_apply,
      iwFullSquare_decomposition d.S k d.period ((2 : ℕ)^n) (one_le_pow₀ (by norm_num))
        (iwCutoffScale C r k Q) ha,
      _root_.add_apply, lp.coeFn_add, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add hlo hhi)
  have hd := highLow_restricted_distribution ordinaryAnnularDyadicFamily F J gLo gHi hGL0 hGH0 hp
    hLoBudget hHiBudget hlarge ht
  intro A
  have hm := mangoldtPositiveFamily.mass_one_le
  have hm' : (1 : ℝ) ≤ primeSquareChebyshevConstant := hm
  have hsmall : t*(J : ℝ)*ordinaryAnnularDyadicFamily.mass*(F.card : ℝ) ≤
      t*(J : ℝ)*primeSquareChebyshevConstant*(F.card : ℝ) := by
    dsimp [ordinaryAnnularDyadicFamily]
    nlinarith [mul_nonneg (mul_nonneg ht.le (Nat.cast_nonneg (α := ℝ) J)) (Nat.cast_nonneg (α := ℝ) F.card)]
  exact (hd A).trans (by linarith)

end PrimeSquares
