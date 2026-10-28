import PrimeSquares.FiniteIntegerVitali

/-!
# Counting the union of intervals with excessive density

The estimate is the elementary counting-measure weak (1,1) argument.
It is proved from finite disjoint selection, not supplied as an input.
-/

open Finset
namespace PrimeSquares

theorem disjoint_interval_intersection_count (U : Finset SparseIntegerInterval)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (F : Finset ℤ) :
    ∑ I ∈ U, (F ∩ I.points).card ≤ F.card := by
  have hd : (U : Set SparseIntegerInterval).PairwiseDisjoint (fun I => F ∩ I.points) := by
    intro I hI J hJ hne
    exact (hU hI hJ hne).mono inter_subset_right inter_subset_right
  rw [← card_biUnion hd]
  apply card_le_card
  intro x hx
  obtain ⟨I, _, hxI⟩ := mem_biUnion.mp hx
  exact (mem_inter.mp hxI).1

theorem integerInterval_weak_counting (S : Finset SparseIntegerInterval)
    (F : Finset ℤ) {t : ℝ} (ht : 0 ≤ t)
    (hbad : ∀ I ∈ S, t * (I.length : ℝ) ≤ (F ∩ I.points).card) :
    t * ((S.biUnion SparseIntegerInterval.points).card : ℝ) ≤ 3 * (F.card : ℝ) := by
  obtain ⟨U, hUS, hU, hcover⟩ := finiteIntegerVitali_cover S
  have hsize : ((S.biUnion SparseIntegerInterval.points).card : ℝ) ≤
      3 * ∑ I ∈ U, (I.length : ℝ) := by
    have hc := (card_le_card hcover).trans
      (card_biUnion_le : (U.biUnion (fun I => I.three.points)).card ≤ _)
    have hc' : ((S.biUnion SparseIntegerInterval.points).card : ℝ) ≤
        ∑ I ∈ U, ((I.three.points).card : ℝ) := by exact_mod_cast hc
    simpa only [integerInterval_card_points, SparseIntegerInterval.three,
      Nat.cast_mul, Nat.cast_ofNat, ← mul_sum] using hc'
  have hdensity : t * ∑ I ∈ U, (I.length : ℝ) ≤ (F.card : ℝ) := by
    calc
      _ = ∑ I ∈ U, t * (I.length : ℝ) := by rw [mul_sum]
      _ ≤ ∑ I ∈ U, ((F ∩ I.points).card : ℝ) := sum_le_sum
        (fun I hI => hbad I (hUS hI))
      _ ≤ _ := by exact_mod_cast disjoint_interval_intersection_count U hU F
  calc
    _ ≤ t * (3 * ∑ I ∈ U, (I.length : ℝ)) := mul_le_mul_of_nonneg_left hsize ht
    _ = 3 * (t * ∑ I ∈ U, (I.length : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdensity (by norm_num)

noncomputable def integerBadIntervalUnion (S : Finset SparseIntegerInterval) (F : Finset ℤ) (t : ℝ) :
    Finset ℤ :=
  (S.filter (fun I => t * (I.length : ℝ) < (F ∩ I.points).card)).biUnion
    SparseIntegerInterval.points

theorem integerBadIntervalUnion_counting (S : Finset SparseIntegerInterval)
    (F : Finset ℤ) {t : ℝ} (ht : 0 ≤ t) :
    t * ((integerBadIntervalUnion S F t).card : ℝ) ≤ 3 * (F.card : ℝ) := by
  apply integerInterval_weak_counting _ F ht
  intro I hI
  exact (mem_filter.mp hI).2.le

theorem integerBadIntervalUnion_packing (S : Finset SparseIntegerInterval)
    (F : Finset ℤ) {L : ℝ} (hL : 0 < L) (hF : F.Nonempty) :
    ((integerBadIntervalUnion S F (64 * (F.card : ℝ) / L)).card : ℝ) ≤ L/4 := by
  have hF0 : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hF
  have h := integerBadIntervalUnion_counting S F
    (t := 64 * (F.card : ℝ) / L) (by positivity)
  have he : (64 * (F.card : ℝ) / L) * L = 64 * (F.card : ℝ) := by
    field_simp
  nlinarith

end PrimeSquares
