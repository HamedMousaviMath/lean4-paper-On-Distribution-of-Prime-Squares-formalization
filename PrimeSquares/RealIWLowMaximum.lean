import PrimeSquares.RealIWAnalyticData

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal lp
namespace PrimeSquares

noncomputable def realIWCutoffScale (C : ℝ) (r k : ℕ) (Q : ℝ) : ℝ :=
  (realIWWidth C r k Q)⁻¹

theorem realIWCutoffScale_four_le {C Q : ℝ} (hC : 2  ≤  C) (hQ : 0  ≤  Q)
    {r : ℕ} (hr : 2  ≤  r) (k : ℕ) : 4  ≤  realIWCutoffScale C r k Q := by
  have hB := realIWDenominatorBound_one_le hC hQ k
  have hp : 1  ≤  realIWDenominatorBound C k Q^(2*r+8) := one_le_pow₀ hB
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  unfold realIWCutoffScale realIWWidth
  rw [inv_inv]
  nlinarith

theorem realIWAdjusted_cutoff (C : ℝ) {Q : ℝ} (hQ : 1  ≤  Q) (r k : ℕ) :
    iwCutoffScale (realIWAdjustedBase C k Q) r k ⌈Q⌉₊ = realIWCutoffScale (C^2) r k Q := by
  unfold iwCutoffScale realIWCutoffScale
  rw [realIWAdjustedBase_width C hQ]

theorem allInputLpMaximalBound_mono_constant
    {T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))} {p : ℝ≥0∞} {K L : ℝ}
    (H : AllInputLpMaximalBound T p K) (hKL : K  ≤  L) : AllInputLpMaximalBound T p L := by
  intro f hf
  obtain ⟨G,hG0,hGm,hGdom,hGn⟩ := H f hf
  exact ⟨G,hG0,hGm,hGdom,hGn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKL) _)⟩

theorem real_iw_full_low_maximal_bound {C Q Z R H S : ℝ}
    (hC : 2  ≤  C) (hCe : Real.exp 1  ≤  C) (hQ : 1  ≤  Q)
    (hZ : 0  ≤  Z) (hR : 0  ≤  R) (hH : 0  ≤  H) (hS : 0  ≤  S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2  ≤  r) (hk : 4  ≤  k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν  ≤  1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β  ≤  1)
    (ha : 2  ≤  realIWCutoffScale (C^2) r k Q) :
    AllInputLpMaximalBound (fun j => iwAnnularLowOperator d.S k d.period ν ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (realIWCutoffScale (C^2) r k Q) ha)
      (ENNReal.ofReal (iwNearOneExponent r))
      (2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q) := by
  let d' := realIWAnalyticData hC hQ hk d
  let : NeZero d'.period := ⟨d'.period_pos.ne'⟩
  have hbounds := realIWAdjustedBase_bounds hC hQ hk
  have hA : 2 ≤ realIWAdjustedBase C k Q := hC.trans hbounds.1
  have hAe : Real.exp 1 ≤ realIWAdjustedBase C k Q := hCe.trans hbounds.1
  have hceil : 1 ≤ ⌈Q⌉₊ := by
    have he : (1:ℝ) ≤ (⌈Q⌉₊:ℝ) := hQ.trans (Nat.le_ceil Q)
    exact_mod_cast he
  have ha' : 2 ≤ iwCutoffScale (realIWAdjustedBase C k Q) r k ⌈Q⌉₊ := by
    rw [realIWAdjusted_cutoff C hQ]
    exact ha
  have Hlow := analytic_iw_full_low_maximal_bound hA hAe hZ hR hH hS
    (rawIWMultiplierInput_mono_base hC hbounds.1 HIW) HCZ HY HRM
    (rawMajorArcSamplingInput_mono_base hC hbounds.1 Hmajor) HShannon HHL HRT
    hr hk hceil d' ν hν hβ0 hβ1 ha'
  have hcost : iwCompleteLowConstant Z R H S*iwMaximalCost (realIWAdjustedBase C k Q) r k ⌈Q⌉₊  ≤ 
      2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q := by
    have h := mul_le_mul_of_nonneg_left (realIWAdjusted_cost hC hQ hr hk)
      (iwCompleteLowConstant_pos hZ hR hH hS).le
    nlinarith only [h]
  have hlow := allInputLpMaximalBound_mono_constant Hlow hcost
  simpa only [d',realIWAnalyticData,realIWAdjusted_cutoff C hQ] using hlow

theorem real_iw_low_all_integer_lp {C Q Z R H S : ℝ}
    (hC : 2  ≤  C) (hCe : Real.exp 1  ≤  C) (hQ : 1  ≤  Q)
    (hZ : 0  ≤  Z) (hR : 0  ≤  R) (hH : 0  ≤  H) (hS : 0  ≤  S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2  ≤  r) (hk : 4  ≤  k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν  ≤  1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β  ≤  1)
    (ha : 2  ≤  realIWCutoffScale (C^2) r k Q)
    (f : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℂ)) :
    ∃ G : ℓ^(ENNReal.ofReal (iwNearOneExponent r))(ℤ,ℝ), (∀ x,0 ≤ G x) ∧
      (∀ j x, ‖iwAnnularLowOperator d.S k d.period ν ((2:ℕ)^j) (one_le_pow₀ (by norm_num)) β
        (realIWCutoffScale (C^2) r k Q) ha
        (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) (iwNearOneExponent_ennreal_le_two hr) f) x‖  ≤  G x) ∧
      ‖G‖  ≤  2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q*‖f‖ := by
  have hlow := real_iw_full_low_maximal_bound hC hCe hQ hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d ν hν hβ0 hβ1 ha
  have hC2 : 2 ≤ C^2 := by nlinarith
  have hcost : 0 ≤ realIWMaximalCost (C^2) r k Q := by
    unfold realIWMaximalCost
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hb := Real.log_nonneg (realIWDenominatorBound_one_le hC2 (by linarith : 0 ≤ Q) k)
    nlinarith [mul_nonneg (Nat.cast_nonneg r) hb]
  exact allInputLpMaximalBound_integerLp _ (iwNearOneExponent_toReal_pos hr)
    (iwNearOneExponent_ennreal_le_two hr)
    (mul_nonneg (mul_nonneg (by norm_num) (iwCompleteLowConstant_pos hZ hR hH hS).le) hcost) hlow f

end PrimeSquares
