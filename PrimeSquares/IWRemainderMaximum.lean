import PrimeSquares.CountableLpMajorant
import PrimeSquares.IWRemainderGeometry
import PrimeSquares.IWAnnularRemainder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

theorem geometric_integer_Lp_majorant {p : ℝ≥0∞} (hp : 1 ≤ p)
    (g : ℕ → ℤ → ℂ) (hg : ∀ n, MemLp (g n) p Measure.count)
    {A q T : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hT : (∑' n : ℕ, q^n) ≤ T) (F : ℝ≥0∞) (hF : F ≠ ∞)
    (hbound : ∀ n, eLpNorm (g n) p Measure.count ≤ ENNReal.ofReal (A*q^n)*F) :
    ∃ H : ℤ → ℝ, (∀ x, 0 ≤ H x) ∧ MemLp H p Measure.count ∧
      (∀ n x, ‖g n x‖ ≤ H x) ∧
      eLpNorm H p Measure.count ≤ ENNReal.ofReal (A*T)*F := by
  have hqS : Summable (fun n : ℕ => q^n) := summable_geometric_of_lt_one hq0 hq1
  have hcost : (∑' n, eLpNorm (g n) p Measure.count) ≤ ENNReal.ofReal (A*T)*F := by
    calc
      _ ≤ ∑' n, ENNReal.ofReal (A*q^n)*F := ENNReal.tsum_le_tsum hbound
      _ = (∑' n, ENNReal.ofReal (A*q^n))*F := ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' n : ℕ, A*q^n)*F := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hA (pow_nonneg hq0 n)) (hqS.mul_left A)]
      _ = ENNReal.ofReal (A*(∑' n : ℕ, q^n))*F := by rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hT hA)) F
  have hsum : ∑' n, eLpNorm (g n) p Measure.count ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF) hcost
  obtain ⟨H, hH0, hHm, hHdom, hHnorm⟩ := countable_integer_Lp_majorant hp g hg hsum
  exact ⟨H, hH0, hHm, hHdom, hHnorm.trans hcost⟩

theorem iw_large_remainder_majorant {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HY : RawYoungMultiplierInput)
    (HRT : RawRieszThorinMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    ∃ H : ℤ → ℝ, (∀ x, 0 ≤ H x) ∧
      MemLp H (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ j x, ‖(iwAnnularLowOperator d.S k d.period ν
          ((2 : ℕ)^j * iwTransitionScale (iwNarrowWidth (iwWidth C r k Q) d.period))
          (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β (iwCutoffScale C r k Q) ha -
        iwAnnularLowOperator d.S k d.period ν
          ((2 : ℕ)^j * iwTransitionScale (iwNarrowWidth (iwWidth C r k Q) d.period))
          (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β
          (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb) f x‖ ≤ H x) ∧
      eLpNorm H (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (2*annularRemainderConstant*(r : ℝ)*iwMultiplierConstant C r k)*
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hP : 1 ≤ d.period := by have h := d.period_pos; omega
  have hδ0 : 0 < δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) hP
  have hδsmall : δ ≤ 1/100 := iwNarrowWidth_small _ hP
  have hδ1 : δ ≤ 1 := by linarith
  have hM := iwTransitionScale_two_le hδ0 hδsmall
  have hbgeom := iwNarrow_inverse_geometry (k := k) (Q := Q) hC hr hP
  let g : ℕ → ℤ → ℂ := fun j =>
    ((iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j * iwTransitionScale δ)
        (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β (iwCutoffScale C r k Q) ha -
      iwAnnularLowOperator d.S k d.period ν ((2 : ℕ)^j * iwTransitionScale δ)
        (by apply Nat.one_le_iff_ne_zero.mpr; dsimp [iwTransitionScale]; positivity) β δ⁻¹ hb) f : ℤ → ℂ)
  have hC0 : 0 ≤ iwMultiplierConstant C r k := iwMultiplierConstant_nonneg (by linarith) r k
  have hA : 0 ≤ iwMultiplierConstant C r k * annularRemainderConstant :=
    mul_nonneg hC0 annularRemainderConstant_pos.le
  have hj (j : ℕ) : MemLp (g j) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      eLpNorm (g j) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal ((iwMultiplierConstant C r k*annularRemainderConstant)*iwRemainderRatio r^j)*
          eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
    have hN : 2 ≤ (2 : ℕ)^j * iwTransitionScale δ := dyadic_annular_scale_lower hM j
    have h := iw_annular_remainder_multiplier hC HIW HY HRT hr hk hN d ν hν hβ0 hβ1
      hbgeom.1 hbgeom.2.1 hb f hf
    rw [integerMultiplier_sub] at h
    change MemLp (g j) _ _ ∧ _ at h
    refine ⟨h.1, h.2.trans ?_⟩
    apply mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_)
    have hd := iw_transition_remainder_decay hr hδ0 hδ1 j
    calc
      _ ≤ iwMultiplierConstant C r k * (annularRemainderConstant*iwRemainderRatio r^j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd annularRemainderConstant_pos.le) hC0
      _ = _ := by ring
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal (iwNearOneExponent r) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (iwNearOneExponent_bounds hr).1.le
  obtain ⟨H, hH0, hHm, hHdom, hHnorm⟩ := geometric_integer_Lp_majorant hp g (fun j => (hj j).1)
    hA (iwRemainderRatio_bounds hr).1.le (iwRemainderRatio_bounds hr).2
    (iwRemainderRatio_sum_bound hr) _ hf.eLpNorm_ne_top (fun j => (hj j).2)
  refine ⟨H, hH0, hHm, hHdom, ?_⟩
  convert hHnorm using 1; congr 2; ring

end PrimeSquares
