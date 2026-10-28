import PrimeSquares.FiniteIntegerSubintervals

/-! # A good point next to each maximal consecutive bad interval -/

open Finset
namespace PrimeSquares

def SparseIntegerInterval.extendLeft (I : SparseIntegerInterval) : SparseIntegerInterval where
  left := I.left-1
  length := I.length+1
  length_pos := by omega

def SparseIntegerInterval.extendRight (I : SparseIntegerInterval) : SparseIntegerInterval where
  left := I.left
  length := I.length+1
  length_pos := by omega

theorem integerInterval_extendLeft_points (I : SparseIntegerInterval) :
    I.extendLeft.points = insert (I.left-1) I.points := by
  ext x
  simp only [integerInterval_mem_points, SparseIntegerInterval.extendLeft,
    Nat.cast_add, Nat.cast_one, mem_insert]
  omega

theorem integerInterval_extendRight_points (I : SparseIntegerInterval) :
    I.extendRight.points = insert (I.left+I.length) I.points := by
  ext x
  simp only [integerInterval_mem_points, SparseIntegerInterval.extendRight,
    Nat.cast_add, Nat.cast_one, mem_insert]
  omega

theorem integerComponent_left_neighbor_good {R I : SparseIntegerInterval} {B : Finset ℤ}
    (hI : I ∈ integerMaximalComponents R B) (hR : I.left-1 ∈ R.points) : I.left-1 ∉ B := by
  intro hB
  have hs := integerMaximalComponents_subset hI
  have hc : I.extendLeft ∈ integerComponentCandidates R B := by
    apply mem_filter.mpr
    rw [mem_integerSubintervals, integerInterval_extendLeft_points]
    exact ⟨insert_subset hR hs.1, insert_subset hB hs.2⟩
  have hh := (mem_filter.mp hI).2 I.extendLeft hc (by
    rw [integerInterval_extendLeft_points]
    exact subset_insert _ _)
  change I.length+1 ≤ I.length at hh
  omega

theorem integerComponent_right_neighbor_good {R I : SparseIntegerInterval} {B : Finset ℤ}
    (hI : I ∈ integerMaximalComponents R B) (hR : I.left+I.length ∈ R.points) :
    I.left+I.length ∉ B := by
  intro hB
  have hs := integerMaximalComponents_subset hI
  have hc : I.extendRight ∈ integerComponentCandidates R B := by
    apply mem_filter.mpr
    rw [mem_integerSubintervals, integerInterval_extendRight_points]
    exact ⟨insert_subset hR hs.1, insert_subset hB hs.2⟩
  have hh := (mem_filter.mp hI).2 I.extendRight hc (by
    rw [integerInterval_extendRight_points]
    exact subset_insert _ _)
  change I.length+1 ≤ I.length at hh
  omega

theorem integerComponent_near_good {R I : SparseIntegerInterval} {B : Finset ℤ}
    (hI : I ∈ integerMaximalComponents R B) {x : ℤ} (hx : x ∈ I.points)
    (hgood : ∃ w ∈ R.points, w ∉ B) :
    ∃ z ∈ R.points, z ∉ B ∧ |x-z| ≤ (I.length : ℤ) := by
  obtain ⟨w, hwR, hwB⟩ := hgood
  have hs := integerMaximalComponents_subset hI
  have hwI : w ∉ I.points := fun h => hwB (hs.2 h)
  have hb := (integerInterval_subset_iff I R).mp hs.1
  rw [integerInterval_mem_points] at hx hwR
  rw [integerInterval_mem_points] at hwI
  by_cases hwl : w < I.left
  · have hzR : I.left-1 ∈ R.points := by
      rw [integerInterval_mem_points]
      constructor <;> omega
    refine ⟨I.left-1, hzR, integerComponent_left_neighbor_good hI hzR, ?_⟩
    rw [abs_le]
    constructor <;> omega
  · have hzR : I.left+I.length ∈ R.points := by
      rw [integerInterval_mem_points]
      constructor <;> omega
    refine ⟨I.left+I.length, hzR, integerComponent_right_neighbor_good hI hzR, ?_⟩
    rw [abs_le]
    constructor <;> omega

theorem integerComponent_length_lt {R I : SparseIntegerInterval} {B : Finset ℤ}
    (hI : I ∈ integerMaximalComponents R B) (hgood : ∃ w ∈ R.points, w ∉ B) :
    I.length < R.length := by
  have hs := integerMaximalComponents_subset hI
  have hl := integerInterval_subset_length hs.1
  by_contra hn
  have he := integerInterval_subset_equal_length hs.1 (by omega : R.length ≤ I.length)
  obtain ⟨w, hw, hwB⟩ := hgood
  exact hwB (hs.2 (he.symm ▸ hw))

theorem integer_good_point_of_quarter_packing (R : SparseIntegerInterval) (B : Finset ℤ)
    (hpack : (B.card : ℝ) ≤ (R.length : ℝ)/4) : ∃ w ∈ R.points, w ∉ B := by
  by_contra! h
  have hc : (R.length : ℝ) ≤ B.card := by
    exact_mod_cast (by simpa only [integerInterval_card_points] using card_le_card h)
  have hp : (0 : ℝ) < R.length := by exact_mod_cast R.length_pos
  linarith

end PrimeSquares
