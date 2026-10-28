import PrimeSquares.FullAdelicIWApplication
import PrimeSquares.FullTaoSamplingApplications

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal lp
namespace PrimeSquares

theorem iw_frequency_in_cyclic_basis {C Q : ℝ} {k : ℕ}
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) {α : ℚ}
    (hα : α ∈ iwFrequencySet d.S k) : α ∈ cyclicTorsionRationals d.period := by
  classical
  rw [cyclicTorsionRationals,Finset.mem_filter,mem_canonicalRationalCenters]
  exact ⟨⟨((iwFrequencySet_mem d.positive α).mp hα).1,
    Nat.le_of_dvd d.period_pos (d.periodic α hα)⟩,d.periodic α hα⟩

theorem rational_fract_circle (α : ℚ) :
    (((Int.fract α : ℚ) : ℝ) : PrimeCircle) = ((α : ℝ) : PrimeCircle) := by
  have hz : (((⌊α⌋ : ℤ) : ℝ) : PrimeCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨⌊α⌋,by simp⟩
  rw [Int.fract,Rat.cast_sub,Rat.cast_intCast,AddCircle.coe_sub,hz,sub_zero]

theorem iw_coverage_all_rational_lifts {C Q : ℝ} {k : ℕ}
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊)
    (α : ℚ) (hα : (α.den : ℝ) ≤ Q) :
    ∃ β ∈ iwFrequencySet d.S k, ((β : ℝ) : PrimeCircle) = ((α : ℝ) : PrimeCircle) := by
  refine ⟨Int.fract α,d.covered ?_,rational_fract_circle α⟩
  rw [mem_canonicalRationalCenters]
  exact ⟨⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
    by rw [Rat.den_intFract]; exact Nat.le_floor hα⟩

theorem iw_coverage_all_fraction_points {C Q : ℝ} {k : ℕ}
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊)
    (q : ℕ) (hq : 0 < q) (hQ : (q : ℝ) ≤ Q) (a : ℤ) :
    ∃ β ∈ iwFrequencySet d.S k,
      ((β : ℝ) : PrimeCircle) = (((a : ℝ)/(q : ℝ)) : PrimeCircle) := by
  have hd : ((a : ℚ)/(q : ℚ)).den ∣ q := by
    have hh : ((((a : ℚ)/(q : ℚ)).den : ℕ) : ℤ) ∣ (q : ℤ) := by
      simpa only [Rat.divInt_eq_div,Int.cast_natCast] using Rat.den_dvd a (q : ℤ)
    exact Int.natCast_dvd_natCast.mp hh
  have hden : (((a : ℚ)/(q : ℚ)).den : ℝ) ≤ Q :=
    (by exact_mod_cast Nat.le_of_dvd hq hd : (((a : ℚ)/(q : ℚ)).den : ℝ) ≤ q).trans hQ
  simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using
    iw_coverage_all_rational_lifts d ((a : ℚ)/(q : ℚ)) hden

theorem fullIntegerKernelMultiplier_single {K : ℤ → ℂ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : FullIntegerKernelMultiplier K p) (n : ℤ) (z : ℂ) (x : ℤ) :
    T.map (lp.single p n z) x = K (x-n)*z := by
  have h := T.agreement {n} (fun _ => z) x
  simpa only [finiteInputLp,Finset.sum_singleton,finiteConvolution] using h

theorem fullIntegerKernelMultiplier_unique {K : ℤ → ℂ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpT : p ≠ ∞) (T U : FullIntegerKernelMultiplier K p) : T.map = U.map := by
  apply ContinuousLinearMap.ext
  intro f
  have hs := lp.hasSum_single hpT f
  have ht := T.map.hasSum hs
  have hu := U.map.hasSum hs
  have he : (fun n : ℤ => T.map (lp.single p n (f n))) =
      (fun n : ℤ => U.map (lp.single p n (f n))) := by
    funext n
    apply lp.ext
    funext x
    rw [fullIntegerKernelMultiplier_single,fullIntegerKernelMultiplier_single]
  rw [he] at ht
  exact ht.unique hu

theorem iw_source_exponent_one_le {r : ℕ} (hr : 2 ≤ r) {p : ℝ}
    (hp : iwNearOneExponent r ≤ p) : 1 ≤ ENNReal.ofReal p := by
  have h : 1 < p := (iwNearOneExponent_bounds hr).1.trans_le hp
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h.le

/-- The three analytic clauses for one shared arithmetic construction and
the literal real-Q width. The full real multiplier operator norm is used,
the major-arc sampling classes are the complete distributional lp classes,
and Shannon sampling includes every p>=1, including infinity. -/
def FullIWSourceAnalyticClauses (C S Q : ℝ) (r k : ℕ)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period] : Prop :=
  (∀ p : ℝ, iwNearOneExponent r ≤ p → p ≤ 2*(r : ℝ) →
    ∀ [Fact (1 ≤ ENNReal.ofReal p)], ∀ B : ℝ, ∀ m : AEBoundedRealSymbol B,
      (∀ᵐ θ ∂volume, realIWWidth C r k Q < |θ| → m.value θ = 0) →
    ∀ A : FullRealLpMultiplier m (ENNReal.ofReal p),
    ∀ ν : ZMod d.period → ℂ, cyclicVariation d.period ν ≤ 1 →
    ∃ T : FullIntegerKernelMultiplier (iwRoughKernel d.period (iwFrequencySet d.S k) ν m)
        (ENNReal.ofReal p), ‖T.map‖ ≤ iwMultiplierConstant C r k*‖A.map‖) ∧
  (∀ p : ℝ, iwNearOneExponent r ≤ p → p ≤ 2*(r : ℝ) →
    ∀ [Fact (1 ≤ ENNReal.ofReal p)],
      FullMajorArcSamplingProperty C r k d.S d.period (realIWWidth C r k Q) p) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ p : ℝ≥0∞, 1 ≤ p → ∀ [Fact (1 ≤ p)],
    ∀ δ : ℝ, 0 < δ → δ ≤ 1/(100*(d.period : ℝ)) →
    ∀ G : ZMod d.period → C(ℝ,V), ∀ hG : ∀ y, MemLp (G y : ℝ → V) p volume,
      (∀ y, RealLpSpectrumIn (cyclicFunctionLp d.period G hG y) (Set.Icc (-δ) δ)) →
    MemLp (fun n : ℤ => G (n : ZMod d.period) (n : ℝ)) p Measure.count ∧
    eLpNorm (fun n : ℤ => G (n : ZMod d.period) (n : ℝ)) p Measure.count ≤
      ENNReal.ofReal S*cyclicRealLpSize d.period p (fun y x => G y x) ∧
    cyclicRealLpSize d.period p (fun y x => G y x) ≤ ENNReal.ofReal S*
      eLpNorm (fun n : ℤ => G (n : ZMod d.period) (n : ℝ)) p Measure.count)

theorem full_iw_source_analytic_clauses {C S Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HIW : RawFullAdelicIWInput C) (Hmajor : RawFullMajorArcSamplingInput C)
    (HShannon : RawFullShannonInput S) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period] :
    FullIWSourceAnalyticClauses C S Q r k d := by
  refine ⟨?_,?_,?_⟩
  · intro p hp0 hp1 inst B m hm A ν hν
    exact source_iw_rough_multiplier_norm hC hQ HIW hr hk d hp0 hp1 m hm A ν hν
  · intro p hp0 hp1 inst
    exact quantitative_real_iw_full_sampling hC hQ Hmajor hr hk d hp0 hp1
  · intro V inst₁ inst₂ inst₃ p hp inst₄ δ _ hδ G hG hband
    exact quantitative_full_shannon_diagonal HShannon V d.period p hp hδ G hG hband

/-- All four clauses of the source quantitative IW proposition, with one
period and one frequency set chosen before the multiplier, exponent,
measure, sampled input and target space. Deep general Tao construction,
IW and sampling theorems remain the explicit independent hypotheses. -/
theorem proposition_quantitative_IW_full {C S : ℝ} (hC : 2 ≤ C)
    (HT : RawTaoArcConstructionInput C) (HIW : RawFullAdelicIWInput C)
    (Hmajor : RawFullMajorArcSamplingInput C) (HShannon : RawFullShannonInput S)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) {Q : ℝ} (hQ : (2 : ℝ)^k ≤ Q) :
    ∃ d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊,
      ∃ inst : NeZero d.period,
        (d.period : ℝ) ≤ (3 : ℝ)^Q ∧
        (∀ α : ℚ, α ∈ Set.Ico (0 : ℚ) 1 → (α.den : ℝ) ≤ Q →
          α ∈ iwFrequencySet d.S k) ∧
        (∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Q → ∀ a : ℤ,
          ∃ β ∈ iwFrequencySet d.S k,
            ((β : ℝ) : PrimeCircle) = (((a : ℝ)/(q : ℝ)) : PrimeCircle)) ∧
        (∀ α ∈ iwFrequencySet d.S k, (α.den : ℝ) ≤ realIWDenominatorBound C k Q) ∧
        IWGood r k d.S (realIWWidth C r k Q) ∧
        @FullIWSourceAnalyticClauses C S Q r k d inst := by
  obtain ⟨d,hP,hcover,hden,_,hgood⟩ := quantitative_iw_real_construction_good hC HT hr hk hQ
  let inst : NeZero d.period := ⟨d.period_pos.ne'⟩
  have hQ0 : 0 ≤ Q := (show (0 : ℝ) ≤ (2 : ℝ)^k by positivity).trans hQ
  exact ⟨d,inst,hP,hcover,iw_coverage_all_fraction_points d,hden,hgood,
    full_iw_source_analytic_clauses hC hQ0 HIW Hmajor HShannon hr hk d⟩

end PrimeSquares
