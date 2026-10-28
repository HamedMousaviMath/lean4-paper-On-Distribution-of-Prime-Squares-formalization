import PrimeSquares.IWFiniteMaximumCost
import PrimeSquares.IWTransitionLogBudget

set_option autoImplicit false
open MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def iwFiniteLowConstant (Z R : ℝ) : ℝ :=
  101*(cutoffL1Constant+R*iwAnnularIncrementCost Z)

theorem iwFiniteLowConstant_nonneg {Z R : ℝ} (hZ : 0≤ Z) (hR : 0≤ R) :
    0≤ iwFiniteLowConstant Z R := by
  have hi := iwAnnularIncrementCost_nonneg hZ
  have hc := cutoffL1Constant_nonneg
  unfold iwFiniteLowConstant
  positivity

theorem iw_short_transition_cost_bound {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z) (hR : 0≤ R)
    {r k Q : ℕ} (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : TaoArcConstructionData C (iwRho k) k Q) :
    iwShortScaleCost C Z R r k (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period))≤
      iwFiniteLowConstant Z R*iwMaximalCost C r k Q := by
  have hc := iw_short_scale_cost_bound (by linarith : 0≤ C) hr Z R k
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period))
  have hj := iw_transition_log_cost_budget hC hr hQ hL d
  have hi := iwAnnularIncrementCost_nonneg hZ
  have hcut := cutoffL1Constant_nonneg
  have hA : 0≤ cutoffL1Constant+R*iwAnnularIncrementCost Z := by positivity
  have hmult := iwMultiplierConstant_one_le hC hr k
  have hmult0 := iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  have hlog : 0≤ Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) :=
    Real.log_nonneg (by have he := Real.add_one_le_exp (1 : ℝ);linarith)
  calc
    _ ≤ (cutoffL1Constant+R*iwAnnularIncrementCost Z)*(r : ℝ)*iwMultiplierConstant C r k*
        Real.log (2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ)) := hc
    _ ≤ (cutoffL1Constant+R*iwAnnularIncrementCost Z)*(r : ℝ)*iwMultiplierConstant C r k*
        (101*Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q))) := by
      gcongr
    _ = (101*(cutoffL1Constant+R*iwAnnularIncrementCost Z))*(r : ℝ)*iwMultiplierConstant C r k*
        Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by ring
    _ ≤ (101*(cutoffL1Constant+R*iwAnnularIncrementCost Z))*(r : ℝ)*(iwMultiplierConstant C r k)^2*
        Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
      gcongr
      nlinarith
    _ = _ := by unfold iwFiniteLowConstant iwMaximalCost;ring

theorem iw_short_transition_maximum {C Z R : ℝ} (hC : 2≤ C) (hCe : Real.exp 1≤ C)
    (hZ : 0≤ Z) (hR : 0≤ R)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k) (hQ : 1≤ Q)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f)
      (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f)
      (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (iwFiniteLowConstant Z R*iwMaximalCost C r k Q)*
        eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have hc : 1≤ Real.log C := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hCe
  have hL := iwDenominatorBound_log_one_le hC hc hk hQ
  obtain ⟨hm,hn⟩ := iw_short_scale_maximum hC hZ hR HIW HCZ HY HRM hr hk d ν hν hβ0 hβ1
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period)) f hf ha
  refine ⟨hm,hn.trans ?_⟩
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (iw_short_transition_cost_bound hC hZ hR hr hQ hL d)) _

end PrimeSquares
