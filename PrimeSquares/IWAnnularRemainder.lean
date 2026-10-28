import PrimeSquares.AnnularCutoffRemainderLp
import PrimeSquares.IWAnnularLp

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

theorem iw_annular_remainder_multiplier {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    (HRT : RawRieszThorinMultiplierInput)
    {r k Q N : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hN : 2 ≤ N)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β b : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb : 0 < b)
    (hab : 2 * iwCutoffScale C r k Q ≤ b) (hb2 : 2 ≤ b) :
    IntegerLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (weightedWidthAnnularBlock (iwFrequencySet d.S k) N (by omega) β
          (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q; linarith)
          (cyclicRationalCoefficient d.period ν) -
        weightedWidthAnnularBlock (iwFrequencySet d.S k) N (by omega) β b hb2
          (cyclicRationalCoefficient d.period ν))
      (iwMultiplierConstant C r k *
        (annularRemainderConstant * (b / (N : ℝ)^2)^((r : ℝ)⁻¹))) := by
  have ha4 := iwCutoffScale_four_le hC hr k Q
  have ha : 0 < iwCutoffScale C r k Q := by linarith
  have hw := iwWidth_pos hC hr k Q
  have haw : 1 ≤ iwCutoffScale C r k Q * iwWidth C r k Q := by
    rw [iwCutoffScale, inv_mul_cancel₀ hw.ne']
  have ha1 : 1 ≤ iwCutoffScale C r k Q * 1 := by linarith
  have hb1 : 1 ≤ b * 1 := by linarith
  have hbw : 1 ≤ b * iwWidth C r k Q := by
    have hm := mul_le_mul_of_nonneg_right hab hw.le
    linarith
  have hsa := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 ha.le ha1
  have hsb := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 hb.le hb1
  have hεa := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 ha.le haw
  have hεb := allAnnularBoundedSymbol_boundary N (by omega) β hβ0.le hβ1 hb.le hbw
  have hs : ∀ x : ℝ, 1 ≤ |x| →
      annularCutoffRemainderSymbol N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b x = 0 := by
    intro x hx
    change _ - _ = (0 : ℂ)
    rw [hsa x hx, hsb x hx, sub_self]
  have hε : ∀ x : ℝ, iwWidth C r k Q ≤ |x| →
      annularCutoffRemainderSymbol N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b x = 0 := by
    intro x hx
    change _ - _ = (0 : ℂ)
    rw [hεa x hx, hεb x hx, sub_self]
  have hp := iwNearOneExponent_bounds hr
  have hp2r : iwNearOneExponent r ≤ 2 * (r : ℝ) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith [hp.2]
  have hcont := annularCutoffRemainder_Lp HY HRT hN hr hβ0 hβ1 ha hb hab
  have hiw := quantitative_iw_multiplier hC HIW hr hk d _ hs hε
    (annularCutoffRemainderSymbol_smooth N (by omega) β hβ0.le hβ1 (iwCutoffScale C r k Q) b)
    ν hν le_rfl hp2r
    (mul_nonneg annularRemainderConstant_pos.le (Real.rpow_nonneg (by positivity) _)) hcont
  change IntegerLpMultiplierBound _ (iwCyclicSymbol _ _ _ _ (_ - _) hs) _ at hiw
  rw [iwCyclicSymbol_sub _ _ _ _ _ _ hsa hsb hs,
    iwCyclicSymbol_all_annular d.S k d.period ν N (by omega) β hβ0.le hβ1
      (iwCutoffScale C r k Q) (by linarith) hsa,
    iwCyclicSymbol_all_annular d.S k d.period ν N (by omega) β hβ0.le hβ1 b hb2 hsb] at hiw
  exact hiw

end PrimeSquares
