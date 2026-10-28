import PrimeSquares.IWShortScaleIncrementMaximum
import PrimeSquares.FiniteDifferenceMaximum

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def iwShortScaleCost (C Z R : ℝ) (r k J : ℕ) : ℝ :=
  iwMultiplierConstant C r k*cutoffL1Constant+
    (R*Real.log (2+(J : ℝ)))*(iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k)

theorem iw_short_scale_maximum {C Z R : ℝ} (hC : 2≤ C) (hZ : 0≤ Z) (hR : 0≤ R)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2≤ iwCutoffScale C r k Q) :
    MemLp (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (initialTemporalMaximum (fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
      (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f) J)
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count≤
      ENNReal.ofReal (iwShortScaleCost C Z R r k J)*
        eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let F : ℕ→ℓ²(ℤ,ℂ) := fun j => iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β (iwCutoffScale C r k Q) ha f
  have h0 := iw_annular_single_multiplier hC HIW HY hr hk d ν hν 1 (by norm_num) hβ0 hβ1 f hf
  change MemLp (F 0 : ℤ→ℂ) _ _ ∧ eLpNorm (F 0 : ℤ→ℂ) _ _≤_ at h0
  have hm := iw_short_scale_increment_maximum hC hZ HIW HCZ HY HRM hr hk d ν hν hβ0 hβ1 J f hf ha
  change MemLp (finitePartialSumMaximum (finiteDifferenceSequence F) J) _ _ ∧
    eLpNorm (finitePartialSumMaximum (finiteDifferenceSequence F) J) _ _≤_ at hm
  have hp := iwNearOneExponent_bounds hr
  have hpen : (1 : ENNReal)≤ ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.1.le
  obtain ⟨hmem,hnorm⟩ := finiteDifferenceSequence_maximum_Lp F J hpen h0.1 hm.1
  refine ⟨hmem,hnorm.trans ((add_le_add h0.2 hm.2).trans_eq ?_)⟩
  have hmult := iwMultiplierConstant_nonneg (by linarith : 0≤ C) r k
  have hinc := iwAnnularIncrementCost_nonneg hZ
  have hcut := cutoffL1Constant_nonneg
  have hlog : 0≤ Real.log (2+(J : ℝ)) :=
    Real.log_nonneg (by have hJ : (0 : ℝ)≤ J := Nat.cast_nonneg J;linarith)
  unfold iwShortScaleCost
  rw [ENNReal.ofReal_add (mul_nonneg hmult hcut)
    (mul_nonneg (mul_nonneg hR hlog) (by positivity)),add_mul,
    ENNReal.ofReal_mul (mul_nonneg hR hlog),mul_assoc]
  simp only [mul_assoc]

end PrimeSquares
