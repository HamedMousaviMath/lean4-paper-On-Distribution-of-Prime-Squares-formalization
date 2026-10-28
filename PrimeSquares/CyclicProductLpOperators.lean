import PrimeSquares.CyclicRealLpBounds

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
namespace PrimeSquares

/-- Normalized finite cyclic Lp norm of a family of actual Banach-space
elements. In applications each element is a full real Lp equivalence class. -/
noncomputable def cyclicFamilyLpSize {E : Type*} [NormedAddCommGroup E]
    (P : ℕ) (p : ℝ≥0∞) (F : ZMod P → E) : ℝ≥0∞ :=
  (P : ℝ≥0∞)^(-(p.toReal)⁻¹)*eLpNorm F p Measure.count

theorem cyclicFamilyLpSize_mono {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (P : ℕ) [NeZero P] (p : ℝ≥0∞) (U : ZMod P → E)
    (V : ZMod P → F) {K : ℝ} (h : ∀ y, ‖U y‖ ≤ K*‖V y‖) :
    cyclicFamilyLpSize P p U ≤ ENNReal.ofReal K*cyclicFamilyLpSize P p V := by
  have hh : eLpNorm U p Measure.count ≤ ENNReal.ofReal K*eLpNorm V p Measure.count :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul AEStronglyMeasurable.of_discrete
      (Filter.Eventually.of_forall h) p
  exact (mul_le_mul_right hh _).trans_eq (by unfold cyclicFamilyLpSize; ring)

theorem cyclicFamilyLpSize_translate {E : Type*} [NormedAddCommGroup E]
    (P : ℕ) [NeZero P] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ∞)
    (F : ZMod P → E) (z : ZMod P) :
    cyclicFamilyLpSize P p (fun y => F (y-z)) = cyclicFamilyLpSize P p F := by
  unfold cyclicFamilyLpSize
  congr 1
  rw [←eLpNorm_norm _ AEStronglyMeasurable.of_discrete,
    ←eLpNorm_norm F AEStronglyMeasurable.of_discrete]
  exact eLpNorm_count_equiv (Equiv.subRight z) (fun y => ‖F y‖) hp0 hpT

theorem cyclicFamilyLpSize_finsetSum {ι E : Type*} [NormedAddCommGroup E]
    (I : Finset ι) (P : ℕ) [NeZero P] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (F : ι → ZMod P → E) :
    cyclicFamilyLpSize P p (fun y => ∑ i ∈ I, F i y) ≤
      ∑ i ∈ I, cyclicFamilyLpSize P p (F i) := by
  unfold cyclicFamilyLpSize
  have hh := eLpNorm_sum_le (μ := Measure.count) (f := F) (s := I) hp
  have he : (∑ i ∈ I, F i) = (fun y => ∑ i ∈ I, F i y) := by
    funext y
    exact Finset.sum_apply y I F
  rw [he] at hh
  simpa only [Finset.mul_sum] using mul_le_mul_right hh
    ((P : ℝ≥0∞)^(-(p.toReal)⁻¹))

/-- Real and cyclic factors acting on the full real Lp fibres, with no L2
intersection or Schwartz restriction. -/
noncomputable def cyclicRealOperator {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (P : ℕ) [NeZero P] (ν : ZMod P → ℂ)
    (A : Lp ℂ p (volume : Measure ℝ) →L[ℂ] Lp ℂ p (volume : Measure ℝ))
    (F : ZMod P → Lp ℂ p (volume : Measure ℝ)) (y : ZMod P) :
    Lp ℂ p (volume : Measure ℝ) := ∑ z : ZMod P, ν z • A (F (y-z))

theorem cyclicRealOperator_Lp_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpT : p ≠ ∞) (P : ℕ) [NeZero P] (ν : ZMod P → ℂ)
    (A : Lp ℂ p (volume : Measure ℝ) →L[ℂ] Lp ℂ p (volume : Measure ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hA : ‖A‖ ≤ K)
    (F : ZMod P → Lp ℂ p (volume : Measure ℝ)) :
    cyclicFamilyLpSize P p (cyclicRealOperator P ν A F) ≤
      ENNReal.ofReal (cyclicVariation P ν*K)*cyclicFamilyLpSize P p F := by
  have hp : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  unfold cyclicRealOperator
  calc
    _ ≤ ∑ z : ZMod P, cyclicFamilyLpSize P p (fun y => ν z • A (F (y-z))) :=
      cyclicFamilyLpSize_finsetSum Finset.univ P hp _
    _ ≤ ∑ z : ZMod P, ENNReal.ofReal (‖ν z‖*K)*
        cyclicFamilyLpSize P p F := by
      apply Finset.sum_le_sum
      intro z _
      have hh := cyclicFamilyLpSize_mono (K := ‖ν z‖*K) P p (fun y => ν z • A (F (y-z)))
        (fun y => F (y-z)) (fun y => by
          rw [norm_smul]
          exact (mul_le_mul_of_nonneg_left
            ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
            (norm_nonneg _)).trans_eq (by ring))
      rwa [cyclicFamilyLpSize_translate P hp0 hpT F z] at hh
    _ = _ := by
      rw [←Finset.sum_mul, ←ENNReal.ofReal_sum_of_nonneg
        (fun z _ => mul_nonneg (norm_nonneg (ν z)) hK)]
      congr 2
      simp only [cyclicVariation, Finset.sum_mul]

theorem cyclicRealOperator_TV_one_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpT : p ≠ ∞) (P : ℕ) [NeZero P] (ν : ZMod P → ℂ)
    (hν : cyclicVariation P ν ≤ 1)
    (A : Lp ℂ p (volume : Measure ℝ) →L[ℂ] Lp ℂ p (volume : Measure ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hA : ‖A‖ ≤ K)
    (F : ZMod P → Lp ℂ p (volume : Measure ℝ)) :
    cyclicFamilyLpSize P p (cyclicRealOperator P ν A F) ≤
      ENNReal.ofReal K*cyclicFamilyLpSize P p F := by
  apply (cyclicRealOperator_Lp_bound hpT P ν A hK hA F).trans
  apply mul_le_mul_left _ _
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end PrimeSquares
