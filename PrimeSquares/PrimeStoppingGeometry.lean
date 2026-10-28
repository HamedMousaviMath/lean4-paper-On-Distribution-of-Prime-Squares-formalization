import PrimeSquares.IntegerBadComponentNeighbors
import PrimeSquares.IntegerIntervalWeakCounting
import PrimeSquares.GoodPointLocalMass

/-!
# The actual bad set, stopping children and admissible remaining scales

All subintervals of the fivefold parent are tested. The weak counting
bound gives quarter packing, and nearby good points control the literal
source local average with the absolute constant 320.
-/

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def primeStoppingThreshold (R : SparseIntegerInterval) (F : Finset ℤ) : ℝ :=
  64 * (F.card : ℝ) / R.length

noncomputable def primeStoppingBadSet (R : SparseIntegerInterval) (F : Finset ℤ) : Finset ℤ :=
  R.points ∩ integerBadIntervalUnion (integerSubintervals R.five) F (primeStoppingThreshold R F)

noncomputable def primeStoppingChildren (R : SparseIntegerInterval) (F : Finset ℤ) :
    Finset SparseIntegerInterval := integerMaximalComponents R (primeStoppingBadSet R F)

theorem primeStoppingBadSet_subset (R : SparseIntegerInterval) (F : Finset ℤ) :
    primeStoppingBadSet R F ⊆ R.points := inter_subset_left

theorem primeStoppingBadSet_packing (R : SparseIntegerInterval) (F : Finset ℤ) :
    ((primeStoppingBadSet R F).card : ℝ) ≤ (R.length : ℝ)/4 := by
  have hR : (0 : ℝ) < R.length := by exact_mod_cast R.length_pos
  by_cases hF : F.Nonempty
  · have hc : ((primeStoppingBadSet R F).card : ℝ) ≤
        (integerBadIntervalUnion (integerSubintervals R.five) F (primeStoppingThreshold R F)).card := by
      exact_mod_cast (card_le_card (inter_subset_right : primeStoppingBadSet R F ⊆ _))
    exact hc.trans (integerBadIntervalUnion_packing _ F hR hF)
  · have he : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    subst F
    simp only [primeStoppingBadSet, primeStoppingThreshold, integerBadIntervalUnion,
      card_empty, Nat.cast_zero, mul_zero, zero_div, empty_inter, zero_mul, lt_self_iff_false,
      filter_false, biUnion_empty, inter_empty]
    positivity

theorem primeStoppingChildren_cover (R : SparseIntegerInterval) (F : Finset ℤ) :
    (primeStoppingChildren R F).biUnion SparseIntegerInterval.points = primeStoppingBadSet R F :=
  integerMaximalComponents_cover (primeStoppingBadSet_subset R F)

theorem primeStoppingChildren_disjoint (R : SparseIntegerInterval) (F : Finset ℤ) :
    (primeStoppingChildren R F : Set SparseIntegerInterval).PairwiseDisjoint
      SparseIntegerInterval.points := integerMaximalComponents_disjoint R _

theorem primeStoppingChildren_geometry {R : SparseIntegerInterval} {F : Finset ℤ}
    {I : SparseIntegerInterval} (hI : I ∈ primeStoppingChildren R F) :
    I.points ⊆ R.points ∧ I.length < R.length := by
  have hg := integer_good_point_of_quarter_packing R _ (primeStoppingBadSet_packing R F)
  exact ⟨(integerMaximalComponents_subset hI).1, integerComponent_length_lt hI hg⟩

theorem primeStopping_good_density {R : SparseIntegerInterval} {F : Finset ℤ} {z : ℤ}
    (hz : z ∈ R.points) (hgood : z ∉ primeStoppingBadSet R F)
    (J : SparseIntegerInterval) (hJ : J.points ⊆ R.five.points) (hzJ : z ∈ J.points) :
    ((F ∩ J.points).card : ℝ) ≤ primeStoppingThreshold R F * (J.length : ℝ) := by
  by_contra! hbad
  apply hgood
  refine mem_inter.mpr ⟨hz, mem_biUnion.mpr ⟨J, ?_, hzJ⟩⟩
  exact mem_filter.mpr ⟨(mem_integerSubintervals R.five J).mpr hJ, hbad⟩

theorem primeStopping_remaining_localMass (R : SparseIntegerInterval) (F : Finset ℤ)
    {N : ℕ} (hN : 1 ≤ N) {x : ℤ} (hx : x ∈ R.points)
    (hrem : ∀ I ∈ primeStoppingChildren R F, x ∈ I.points → I.length < N^2) :
    sourceLocalMass N (finiteIndicatorLp F 1) x ≤ 320 * ((F.card : ℝ) / R.length) := by
  have hR : (0 : ℝ) < R.length := by exact_mod_cast R.length_pos
  have hclose : ∃ z ∈ R.points, z ∉ primeStoppingBadSet R F ∧
      |((x-z : ℤ) : ℝ)| ≤ (N : ℝ)^2 := by
    by_cases hbad : x ∈ primeStoppingBadSet R F
    · have hcov : x ∈ (primeStoppingChildren R F).biUnion SparseIntegerInterval.points := by
        rw [primeStoppingChildren_cover]
        exact hbad
      obtain ⟨I, hI, hxI⟩ := mem_biUnion.mp hcov
      obtain ⟨z, hzR, hzB, hdist⟩ := integerComponent_near_good hI hxI
        (integer_good_point_of_quarter_packing R _ (primeStoppingBadSet_packing R F))
      refine ⟨z, hzR, hzB, ?_⟩
      have hd : |((x-z : ℤ) : ℝ)| ≤ (I.length : ℝ) := by exact_mod_cast hdist
      have hl : (I.length : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast (hrem I hI hxI).le
      exact hd.trans hl
    · exact ⟨x, hx, hbad, by simp⟩
  obtain ⟨z, hzR, hzB, hdist⟩ := hclose
  have ht : (F.card : ℝ) / R.length ≤ primeStoppingThreshold R F := by
    have hp : 0 ≤ (F.card : ℝ) / R.length := div_nonneg (Nat.cast_nonneg _) hR.le
    dsimp [primeStoppingThreshold]
    rw [mul_div_assoc]
    nlinarith
  have h := goodPoint_sourceLocalMass R F ht hN hx hdist
    (fun J hJ hzJ => primeStopping_good_density hzR hzB J hJ hzJ)
  calc
    _ ≤ 5 * primeStoppingThreshold R F := h
    _ = _ := by dsimp [primeStoppingThreshold]; ring

end PrimeSquares
