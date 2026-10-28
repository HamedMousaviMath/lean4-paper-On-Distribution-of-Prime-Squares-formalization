import PrimeSquares.IWAllInputLowMaximum
import PrimeSquares.MangoldtAnnularPositiveFamily
import PrimeSquares.HighLowRestrictedDistribution

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal lp
namespace PrimeSquares

theorem iwPrimeHighOperator_scale_congr {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (Γ : Finset ℚ) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (he : N = M)
    (a : ℝ) (ha : 2 ≤ a) (E₀ : Option PageZeroDatum) (Q : ℝ) :
    iwPrimeHighOperator D Γ N hN a ha E₀ Q = iwPrimeHighOperator D Γ M hM a ha E₀ Q := by
  cases he
  rfl

theorem primeHigh_indicator_power_budget {Q K : ℝ} (hQ : 0 < Q)
    (F : Finset ℤ) (g : lp (fun _ : ℤ => ℝ) 2) (hg : ∀ x, 0 ≤ g x)
    (hnorm : ‖g‖ ≤ K*Q^(-(1/4 : ℝ))*‖finiteIndicatorLp F 2‖) :
    FinitePowerBudget g 2 (K^2*Q^(-(1/2 : ℝ))*(F.card : ℝ)) := by
  have hquarter : (Q^(-(1/4 : ℝ)))^2 = Q^(-(1/2 : ℝ)) := by
    rw [←Real.rpow_two, ←Real.rpow_mul hQ.le]
    congr 1
    norm_num
  have hcard : ‖finiteIndicatorLp F 2‖^2 = (F.card : ℝ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      finiteIndicatorLp_norm_power F (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsq := pow_le_pow_left₀ (norm_nonneg g) hnorm 2
  rw [mul_pow, mul_pow, hquarter, hcard] at hsq
  intro A
  have h := finitePowerBudget_lp (by norm_num : 0 < (2 : ENNReal).toReal) g hg A
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  simpa only [Real.rpow_two] using h.trans hsq

theorem iw_prime_annular_restricted_distribution {c C Cb Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hc : 0 < c) (HP : RawPageUniquenessInput c)
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
      TestedDistributionBound (positiveMaximal mangoldtAnnularDyadicFamily (finiteIndicator F)) (1/t)
        (t*(J : ℝ)*primeSquareChebyshevConstant*(F.card : ℝ)+
          (2*t)^(iwNearOneExponent r)*
            ((2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)^(iwNearOneExponent r)*(F.card : ℝ))+
          4*t^2*(KH^2*(Q : ℝ)^(-(1/2 : ℝ))*(F.card : ℝ))) := by
  obtain ⟨Cstart, KH, hstart0, hKH, hHigh⟩ := iw_prime_high_source_scale hCb HB hc HP D
  refine ⟨Cstart, KH, hstart0, hKH, ?_⟩
  intro r k Q J hr hk hQ hJ hstart F t ht
  have hQ1 : 1 ≤ Q := (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))).trans hQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hM : 2 ≤ (2 : ℕ)^J := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hJ
  obtain ⟨d, _hgood, _hden, E₀, hsmall, hHi⟩ := hHigh C hC hCe HT r k Q ((2 : ℕ)^J) hr hk hQ hM hstart
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  have ha : 2 ≤ iwCutoffScale C r k Q := by have h := iwCutoffScale_four_le hC hr k Q; linarith
  have hpR := iwNearOneExponent_toReal_pos hr
  have hp : 0 < iwNearOneExponent r := lt_trans zero_lt_one (iwNearOneExponent_bounds hr).1
  have hp0 : 0 ≤ iwNearOneExponent r := hp.le
  have hf := finiteInputLp_count_memLp F (fun _ => (1 : ℂ)) hpR
  rw [finiteInputLp_one] at hf
  have hLow := iw_prime_low_maximal_bound D hC hCe hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
    hr hk hQ1 d E₀ (fun E hE => (hsmall E hE).1) ha
  obtain ⟨gLo, hGL0, hGLm, hGLdom, hGLnorm⟩ := hLow (finiteIndicatorLp F 2) hf
  obtain ⟨gHi, hGH0, hGHdom, hGHnorm⟩ := hHi (finiteIndicatorLp F 2)
  have hKlow : 0 ≤ 2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q :=
    mul_nonneg (mul_nonneg (by norm_num) (iwCompleteLowConstant_pos hZ hR hH hS).le)
      ((by positivity : 0 ≤ (r : ℝ)*(iwMultiplierConstant C r k)^2).trans (iwMaximalCost_lower_bounds hC hr k Q).1)
  have hLoBudget : FinitePowerBudget gLo (iwNearOneExponent r)
      ((2*iwCompleteLowConstant Z R H S*iwMaximalCost C r k Q)^(iwNearOneExponent r)*(F.card : ℝ)) := by
    simpa only [ENNReal.toReal_ofReal hp0] using
      count_Lp_indicator_power_budget hpR hGLm hGL0 F hKlow hGLnorm
  have hHiBudget := primeHigh_indicator_power_budget hQR F gHi hGH0 hGHnorm
  have hlarge : ∀ n : ℕ, J ≤ n → ∀ x,
      ‖positiveAverage mangoldtAnnularDyadicFamily n (finiteIndicator F) x‖ ≤ gLo x+gHi x := by
    intro n hn x
    have hscale : (2 : ℕ)^(n-J)*(2 : ℕ)^J = (2 : ℕ)^n := by
      rw [←pow_add, Nat.sub_add_cancel hn]
    have hprod : 1 ≤ (2 : ℕ)^(n-J)*(2 : ℕ)^J := by
      have hs := dyadic_annular_scale_lower hM (n-J)
      omega
    have hhi := hGHdom (n-J) x
    rw [iwPrimeHighOperator_scale_congr D (iwFrequencySet d.S k) hprod
      (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hscale (iwCutoffScale C r k Q) ha E₀ Q] at hhi
    have hlo := hGLdom n x
    change ‖positiveAverage mangoldtAnnularDyadicFamily n (finiteIndicatorLp F 2 : ℤ → ℂ) x‖ ≤ _
    rw [mangoldtAnnularDyadicFamily_apply,
      iwPrime_decomposition D (iwFrequencySet d.S k) ((2 : ℕ)^n) (one_le_pow₀ (by norm_num))
        (iwCutoffScale C r k Q) ha E₀ Q,
      _root_.add_apply, lp.coeFn_add, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add hlo hhi)
  exact highLow_restricted_distribution mangoldtAnnularDyadicFamily F J gLo gHi hGL0 hGH0 hp
    hLoBudget hHiBudget hlarge ht

end PrimeSquares
