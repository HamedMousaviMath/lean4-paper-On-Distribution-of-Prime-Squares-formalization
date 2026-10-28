import PrimeSquares.RealIWLowMaximum

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal lp
namespace PrimeSquares

theorem rawTaoArcConstructionInput_mono_base {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D)
    (HT : RawTaoArcConstructionInput C) : RawTaoArcConstructionInput D := by
  intro ρ hρ0 hρ1 Q hQ
  obtain ⟨d⟩ := HT ρ hρ0 hρ1 Q hQ
  refine ⟨{ S := d.S
            positive := d.positive
            coprime := d.coprime
            period := d.period
            period_pos := d.period_pos
            period_bound := d.period_bound
            covered := d.covered
            periodic := d.periodic
            component_bound := ?_ }⟩
  intro s hs
  exact (d.component_bound s hs).trans (Real.rpow_le_rpow hC hCD
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

/-- The real-Q geometric construction together with its actual all-input low
maximum. The absolute constant in the displayed source parameters is C^2. -/
theorem real_iw_source_construction_and_low {C Q Z R H S : ℝ}
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HT : RawTaoArcConstructionInput C) (HIW : RawIWMultiplierInput C)
    (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : (2:ℝ)^k ≤ Q) :
    ∃ d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊,
      (d.period:ℝ) ≤ (3:ℝ)^Q ∧
      (∀ a : ℚ,a ∈ Set.Ico (0:ℚ) 1 → (a.den:ℝ) ≤ Q → a ∈ iwFrequencySet d.S k) ∧
      (∀ a ∈ iwFrequencySet d.S k,(a.den:ℝ) ≤ realIWDenominatorBound (C^2) k Q) ∧
      IWGood r k d.S (realIWWidth (C^2) r k Q) ∧
      (let : NeZero d.period := ⟨d.period_pos.ne'⟩
       ∀ (ν : ZMod d.period → ℂ), cyclicVariation d.period ν ≤ 1 →
        ∀ β : ℝ, 0 < β → β ≤ 1 →
        AllInputLpMaximalBound (fun j => iwAnnularLowOperator d.S k d.period ν ((2:ℕ)^j)
          (one_le_pow₀ (by norm_num)) β (realIWCutoffScale (C^2) r k Q)
          (by have ha := realIWCutoffScale_four_le (by nlinarith : 2≤C^2)
                ((show (0:ℝ)≤(2:ℝ)^k by positivity).trans hQ) hr k
              linarith))
          (ENNReal.ofReal (iwNearOneExponent r))
          (2*iwCompleteLowConstant Z R H S*realIWMaximalCost (C^2) r k Q)) := by
  have hC2 : 2≤C^2 := by nlinarith
  have hQ1 : 1≤Q := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hQ
  have hT := rawTaoArcConstructionInput_mono_base (by linarith : 0≤C) (by nlinarith : C≤C^2) HT
  obtain ⟨d,hP,hcover,hden,_,hgood⟩ := quantitative_iw_real_construction_good hC2 hT hr hk hQ
  refine ⟨d,hP,hcover,hden,hgood,?_⟩
  let : NeZero d.period := ⟨d.period_pos.ne'⟩
  dsimp only
  intro ν hν β hβ0 hβ1
  exact real_iw_full_low_maximal_bound hC hCe hQ1 hZ hR hH hS HIW HCZ HY HRM Hmajor
    HShannon HHL HRT hr hk d ν hν hβ0 hβ1 _

end PrimeSquares
