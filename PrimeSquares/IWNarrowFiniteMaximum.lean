import PrimeSquares.IWNarrowLiftIdentity
import PrimeSquares.IWRemainderGeometry

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ContDiff ENNReal lp
namespace PrimeSquares

theorem iwFiniteCutoffLift_size {C : ℝ} (hC : 2 ≤ C)
    (HIW : RawIWMultiplierInput C) (HS : RawMajorArcSamplingInput C) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q) :
    cyclicRealLpSize d.period (ENNReal.ofReal (iwNearOneExponent r))
      (fun y x => finiteCutoffLift (iwFrequencySet d.S k) d.period (iwCutoffScale C r k Q) ha F f y x) ≤
      ENNReal.ofReal ((iwMultiplierConstant C r k)^2*cutoffL1Constant)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  have ha0 : 0 ≤ iwCutoffScale C r k Q := by linarith
  have hs := continuousCutoffSymbol_boundary ha0 (by linarith : 1 ≤ iwCutoffScale C r k Q*1)
  have hn := continuousCutoffSymbol_boundary ha0 (by linarith : 1 ≤ iwCutoffScale C r k Q*(1/2))
  have hwidth : 1 ≤ iwCutoffScale C r k Q*iwWidth C r k Q := by
    rw [iwCutoffScale, inv_mul_cancel₀ (iwWidth_pos hC hr k Q).ne']
  have hε := continuousCutoffSymbol_boundary ha0 hwidth
  have hLp := continuousCutoffMultiplier_Lp HY (by linarith : 0 < iwCutoffScale C r k Q)
    (iwNearOneExponent_bounds hr).1.le
  have h := iw_finite_lift_size hC HIW HS hr hk d (continuousCutoffSymbol (iwCutoffScale C r k Q))
    hs hn hε (continuousCutoffSymbol_smooth _) cutoffL1Constant_nonneg hLp F f hf
  simpa only [finiteCutoffLift, cyclicSynthesisSchwartz_apply] using h

noncomputable def iwNarrowLowConstant (H S : ℝ) : ℝ :=
  2*S*H*cutoffL1Constant^2

theorem iw_narrow_finite_maximum {C H S : ℝ} (hC : 2 ≤ C) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HY : RawYoungMultiplierInput)
    {r k Q : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k Q) [NeZero d.period]
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (I : Finset ℕ) (N : ℕ → ℕ) (hN : ∀ i, 2 ≤ N i)
    (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : MemLp (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count)
    (ha : 2 ≤ iwCutoffScale C r k Q)
    (hb : 2 ≤ (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹) :
    MemLp (finiteCoordinateMaximum I (fun i (n : ℤ) =>
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β
        (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) n))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ∧
    eLpNorm (finiteCoordinateMaximum I (fun i (n : ℤ) =>
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β
        (iwNarrowWidth (iwWidth C r k Q) d.period)⁻¹ hb (finiteInputLp F f 2) n))
      (ENNReal.ofReal (iwNearOneExponent r)) Measure.count ≤
      ENNReal.ofReal (iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2)*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal (iwNearOneExponent r)) Measure.count := by
  let p := iwNearOneExponent r
  have hp := iwNearOneExponent_bounds hr
  have hp2 : p ≤ 2 := by dsimp only [p]; linarith [hp.2]
  have hpen : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.1.le
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hP : 1 ≤ d.period := by have h := d.period_pos; omega
  have hδ : 0 < δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) hP
  have hbgeom := iwNarrow_inverse_geometry (k := k) (Q := Q) hC hr hP
  let W := finiteCutoffLift (iwFrequencySet d.S k) d.period (iwCutoffScale C r k Q) ha F f
  let E := cyclicConvolutionSchwartz d.period ν W
  let G : ℕ → ZMod d.period → SchwartzMap ℝ ℂ := fun i y =>
    annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 δ⁻¹ hb (E y)
  have hband : ∀ i ∈ I, ∀ y : ZMod d.period, ∀ θ : ℝ, δ ≤ |θ| → 𝓕 (G i y : ℝ → ℂ) θ = 0 := by
    intro i _ y θ hθ
    apply annularSchwartzOutput_band (N i) (by have h := hN i; omega) β hβ0 hβ1 hb _ (E y) θ hθ
    rw [inv_mul_cancel₀ hδ.ne']
  have hSh := HShannon d.period δ hδ (iwNarrowWidth_le_period _ _) p hp.1.le hp2 I G hband
  have hpoint (i : ℕ) (n : ℤ) : G i (n : ZMod d.period) (n : ℝ) =
      iwAnnularLowOperator d.S k d.period ν (N i) (by have h := hN i; omega) β δ⁻¹ hb (finiteInputLp F f 2) n := by
    exact iw_narrow_lift_diagonal d.S k d.period d.periodic ν (N i) (by have h := hN i; omega)
      β hβ0 hβ1 ha hb hbgeom.2.1 F f n
  simp_rw [hpoint] at hSh
  refine ⟨hSh.1, hSh.2.trans ?_⟩
  have hW := iwFiniteCutoffLift_size hC HIW Hmajor HY hr hk d F f hf ha
  have hE := cyclicConvolutionSchwartz_Lp d.period hpen ENNReal.ofReal_ne_top ν W
  have hEW : cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => E y x) ≤
      cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => W y x) := by
    refine hE.trans ?_
    have htv : ENNReal.ofReal (cyclicVariation d.period ν) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hν
    simpa only [one_mul] using mul_le_mul_left htv
      (cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => W y x))
  have hreal := cyclic_annularSchwartzOutput_maximum hH HHL HY d.period hp.1 hp2 hβ0 hβ1 hb I N hN E
  have hA : 0 ≤ (H/(p-1))*cutoffL1Constant := mul_nonneg (div_nonneg hH (by linarith [hp.1])) cutoffL1Constant_nonneg
  have hcoef : S*((H/(p-1))*cutoffL1Constant)*((iwMultiplierConstant C r k)^2*cutoffL1Constant) ≤
      iwNarrowLowConstant H S*(r : ℝ)*(iwMultiplierConstant C r k)^2 := by
    have hnear := iwNearOneExponent_cost hr hH
    have hmult := mul_le_mul_of_nonneg_left hnear
      (mul_nonneg (mul_nonneg hS (sq_nonneg cutoffL1Constant)) (sq_nonneg (iwMultiplierConstant C r k)))
    unfold iwNarrowLowConstant
    dsimp only [p]
    nlinarith only [hmult]
  calc
    _ ≤ ENNReal.ofReal S *
        (ENNReal.ofReal ((H/(p-1))*cutoffL1Constant)*
          cyclicRealLpSize d.period (ENNReal.ofReal p) (fun y x => E y x)) :=
      mul_le_mul_right hreal _
    _ ≤ ENNReal.ofReal S *
        (ENNReal.ofReal ((H/(p-1))*cutoffL1Constant)*
          (ENNReal.ofReal ((iwMultiplierConstant C r k)^2*cutoffL1Constant)*
            eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal p) Measure.count)) := by
      apply mul_le_mul_right
      exact mul_le_mul_right (hEW.trans hW) _
    _ = ENNReal.ofReal (S*((H/(p-1))*cutoffL1Constant)*((iwMultiplierConstant C r k)^2*cutoffL1Constant))*
        eLpNorm (finiteInputLp F f 2 : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      rw [←mul_assoc, ←mul_assoc, ←ENNReal.ofReal_mul hS, ←ENNReal.ofReal_mul (mul_nonneg hS hA)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoef) _

end PrimeSquares
