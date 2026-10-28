import PrimeSquares.IWAnnularSignedIdentity

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem iw_annular_single_multiplier {C : ℝ} (hC : 2≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    (N : ℕ) (hN : 1≤ N) {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β (iwCutoffScale C r k Q)
        (by have h := iwCutoffScale_four_le hC hr k Q;linarith) (cyclicRationalCoefficient d.period ν))
      (iwMultiplierConstant C r k*cutoffL1Constant) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0 < iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale,inv_mul_cancel₀ hw.ne']
  have ha1 : 1≤ iwCutoffScale C r k Q*1 := by linarith
  have hs := allAnnularBoundedSymbol_boundary N hN β hβ0.le hβ1 ha.le ha1
  have hε := allAnnularBoundedSymbol_boundary N hN β hβ0.le hβ1 ha.le haw
  have hpr := iwNearOneExponent_bounds hr
  have hp2r : iwNearOneExponent r≤2*(r : ℝ) := by
    have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
    linarith [hpr.2]
  have hcont := annularCutoffYoungMultiplier_Lp HY hN hβ0 hβ1 ha hpr.1.le
  have hiw := quantitative_iw_multiplier hC HIW hr hk d _ hs hε
    (annularCutoffSymbol_contDiff hN β (iwCutoffScale C r k Q)) ν hν
    le_rfl hp2r cutoffL1Constant_nonneg hcont
  rw [iwCyclicSymbol_all_annular d.S k d.period ν N hN β hβ0.le hβ1
    (iwCutoffScale C r k Q) (by linarith) hs] at hiw
  exact hiw

theorem iw_annular_signed_increments {C Z : ℝ} (hC : 2≤ C) (hZ : 0≤ Z)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2≤ r) (hk : 4≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period→ℂ) (hν : cyclicVariation d.period ν≤1)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) (f : ℓ²(ℤ,ℂ))
    (hf : MeasureTheory.MemLp (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count) :
    MeasureTheory.MemLp (iwAnnularSignedOperator d.S k d.period ν β (iwCutoffScale C r k Q)
      (by have h := iwCutoffScale_four_le hC hr k Q;linarith) J σ f : ℤ→ℂ)
      (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count ∧
    MeasureTheory.eLpNorm (iwAnnularSignedOperator d.S k d.period ν β (iwCutoffScale C r k Q)
      (by have h := iwCutoffScale_four_le hC hr k Q;linarith) J σ f : ℤ→ℂ)
      (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count≤
      ENNReal.ofReal (iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k)*
        MeasureTheory.eLpNorm (f : ℤ→ℂ) (ENNReal.ofReal (iwNearOneExponent r)) MeasureTheory.Measure.count := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha0 : 0≤ iwCutoffScale C r k Q := by linarith
  have ha1 : 1≤ iwCutoffScale C r k Q*1 := by linarith
  have hs := continuousAnnularSignedSymbol_boundary β hβ0.le hβ1 J σ ha0 ha1
  have h := iw_signed_annular_multiplier hC hZ HIW HCZ HY hr hk d ν hν hβ0 hβ1 J σ hσ hs f hf
  rw [iw_signed_annular_operator_identity d.S k d.period ν β hβ0.le hβ1
    (iwCutoffScale C r k Q) (by linarith) J σ hs] at h
  exact h

end PrimeSquares
