import PrimeSquares.RealIWParameters
import PrimeSquares.IWMultiplierInterface
import PrimeSquares.IWSamplingSpaces

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PrimeSquares

theorem real_iw_goodness_from_floor {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) :
    IWGood r k d.S (realIWWidth C r k Q) := by
  have hwidth : realIWWidth C r k Q ≤ iwWidth C r k ⌊Q⌋₊ := by
    simpa only [realIWWidth_nat] using realIWWidth_antitone hC hr hk
      (Nat.cast_nonneg ⌊Q⌋₊) (Nat.floor_le hQ)
  exact iwGood_of_smaller_width (quantitative_iw_goodness hC hr hk d)
    (realIWWidth_pos hC hr hQ k) hwidth

theorem real_iw_geometry_from_floor {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) :
    (d.period:ℝ) ≤ (3:ℝ)^Q ∧
      (∀ a : ℚ,a ∈ Set.Ico (0:ℚ) 1 → (a.den:ℝ) ≤ Q → a ∈ iwFrequencySet d.S k) ∧
      (∀ a ∈ iwFrequencySet d.S k,(a.den:ℝ) ≤ realIWDenominatorBound C k Q) ∧
      (∀ s ∈ d.S,(s:ℝ) ≤ C^((k:ℝ)*Q^(iwRho k/2))) ∧
      IWGood r k d.S (realIWWidth C r k Q) := by
  have hf : (⌊Q⌋₊:ℝ)≤Q := Nat.floor_le hQ
  refine ⟨?_,?_,?_,?_,real_iw_goodness_from_floor hC hQ hr hk d⟩
  · calc
      _ ≤ (3:ℝ)^(⌊Q⌋₊:ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast d.period_bound
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hf
  · intro a ha hden
    apply d.covered
    rw [mem_canonicalRationalCenters]
    exact ⟨ha,Nat.le_floor hden⟩
  · intro a ha
    have hmono : iwDenominatorBound C k ⌊Q⌋₊ ≤ realIWDenominatorBound C k Q := by
      simpa only [realIWDenominatorBound_nat] using
        realIWDenominatorBound_mono hC hk (Nat.cast_nonneg ⌊Q⌋₊) hf
    exact (taoArc_denominator_bound hC d hk ha).trans hmono
  · intro s hs
    apply (d.component_bound s hs).trans
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤C)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg ⌊Q⌋₊) hf
        (div_nonneg (iwRho_bounds hk).1.le (by norm_num))) (Nat.cast_nonneg _))

theorem quantitative_iw_real_construction_good {C Q : ℝ} (hC : 2 ≤ C)
    (HT : RawTaoArcConstructionInput C) {r k : ℕ}
    (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ : (2:ℝ)^k ≤ Q) :
    ∃ d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊,
      (d.period:ℝ) ≤ (3:ℝ)^Q ∧
      (∀ a : ℚ,a ∈ Set.Ico (0:ℚ) 1 → (a.den:ℝ) ≤ Q → a ∈ iwFrequencySet d.S k) ∧
      (∀ a ∈ iwFrequencySet d.S k,(a.den:ℝ) ≤ realIWDenominatorBound C k Q) ∧
      (∀ s ∈ d.S,(s:ℝ) ≤ C^((k:ℝ)*Q^(iwRho k/2))) ∧
      IWGood r k d.S (realIWWidth C r k Q) := by
  have hfloor : (2:ℕ)^k ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  have hQ0 : 0 ≤ Q := (show (0:ℝ)≤(2:ℝ)^k by positivity).trans hQ
  obtain ⟨d,_,_⟩ := quantitative_iw_construction_good hC HT hr hk hfloor
  exact ⟨d,real_iw_geometry_from_floor hC hQ0 hr hk d⟩

theorem quantitative_real_iw_smooth_multiplier {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HIW : RawIWMultiplierInput C) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    (m : BoundedContinuousFunction ℝ ℂ) (hs : ∀ x : ℝ,1 ≤ |x| → m x=0)
    (hε : ∀ x : ℝ,realIWWidth C r k Q ≤ |x| → m x=0)
    (hm : ContDiff ℝ ∞ (m:ℝ → ℂ))
    (ν : ZMod d.period → ℂ) (hν : cyclicVariation d.period ν ≤ 1)
    {p K : ℝ} (hp0 : iwNearOneExponent r ≤ p) (hp1 : p ≤ 2*(r:ℝ))
    (hK : 0 ≤ K) (hbound : RealLpMultiplierBound (ENNReal.ofReal p) m K) :
    IntegerLpMultiplierBound (ENNReal.ofReal p)
      (iwCyclicSymbol d.S k d.period ν m hs) (iwMultiplierConstant C r k*K) := by
  exact HIW r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (realIWWidth C r k Q) (real_iw_goodness_from_floor hC hQ hr hk d)
      m hs hε hm ν hν p hp0 hp1 K hK hbound

theorem quantitative_real_iw_schwartz_sampling {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HS : RawMajorArcSamplingInput C) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    {p : ℝ} (hp0 : iwNearOneExponent r ≤ p) (hp1 : p ≤ 2*(r:ℝ))
    (u : ℚ → SchwartzMap ℝ ℂ)
    (hu : ∀ α ∈ iwFrequencySet d.S k,∀ θ : ℝ,
      realIWWidth C r k Q ≤ |θ| → 𝓕 (u α:ℝ → ℂ) θ=0)
    (hdiag : MemLp (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
      (ENNReal.ofReal p) Measure.count) :
    cyclicRealLpSize d.period (ENNReal.ofReal p) (cyclicSynthesis (iwFrequencySet d.S k) d.period u) ≤
      ENNReal.ofReal (iwMultiplierConstant C r k)*
        eLpNorm (cyclicDiagonal d.period (cyclicSynthesis (iwFrequencySet d.S k) d.period u))
          (ENNReal.ofReal p) Measure.count := by
  exact HS r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (realIWWidth C r k Q) (real_iw_goodness_from_floor hC hQ hr hk d) p hp0 hp1 u hu hdiag

end PrimeSquares
