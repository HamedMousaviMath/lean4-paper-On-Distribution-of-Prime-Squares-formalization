import PrimeSquares.IWNarrowFiniteMaximum
import PrimeSquares.UniformFiniteLpMaximum

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

theorem iwNarrowLowConstant_nonneg {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) :
    0 ≤ iwNarrowLowConstant H S := by
  unfold iwNarrowLowConstant
  positivity

theorem iw_narrow_integer_majorant {C H S : ℝ} (hC : 2 ≤ C) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    ∃ G : ℤ → ℝ, (∀ x, 0 ≤ G x) ∧
      MemLp G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
      (∀ (N : ℕ) (hN : 2 ≤ N) (x : ℤ),
        ‖iwAnnularLowOperator d.S k d.period ν N (by omega) β
          (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) x‖ ≤ G x) ∧
      eLpNorm G (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
        ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
          eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let g : ℕ → ℤ → ℂ := fun j x =>
    iwAnnularLowOperator d.S k d.period ν (j+2) (by omega) β
      (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) x
  have hp0 : ENNReal.ofReal (iwNearOneExponent r) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one (iwNearOneExponent_bounds hr).1))
  have hB : ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
      eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  obtain ⟨G, hG0, hGm, hGdom, hGnorm⟩ := uniform_finite_integer_Lp_majorant hp0 g hB
    (fun I => iw_narrow_finite_maximum hC hH hS HIW Hmajor HShannon HHL HY hr hk d ν hν hβ0 hβ1
      I (fun j => j+2) (fun _ => by omega) F f hf ha hb)
  refine ⟨G, hG0, hGm, ?_, hGnorm⟩
  intro N hN x
  have h := hGdom (N-2) x
  simpa only [g, Nat.sub_add_cancel hN] using h

end PrimeSquares
