import PrimeSquares.SparseIntegerIntervals

/-! # Integer interval inclusion and connected unions -/

open Finset
namespace PrimeSquares

theorem integerInterval_left_mem (I : SparseIntegerInterval) : I.left ∈ I.points := by
  rw [integerInterval_mem_points]
  have := I.length_pos
  constructor <;> omega

theorem integerInterval_last_mem (I : SparseIntegerInterval) :
    I.left + I.length - 1 ∈ I.points := by
  rw [integerInterval_mem_points]
  have := I.length_pos
  constructor <;> omega

theorem integerInterval_subset_iff (I J : SparseIntegerInterval) :
    I.points ⊆ J.points ↔ J.left ≤ I.left ∧ I.left + I.length ≤ J.left + J.length := by
  constructor
  · intro h
    have hl := (integerInterval_mem_points J I.left).mp (h (integerInterval_left_mem I))
    have hr := (integerInterval_mem_points J (I.left+I.length-1)).mp
      (h (integerInterval_last_mem I))
    constructor <;> omega
  · rintro ⟨hl, hr⟩ x hx
    rw [integerInterval_mem_points] at hx ⊢
    constructor <;> omega

theorem integerInterval_subset_length {I J : SparseIntegerInterval} (h : I.points ⊆ J.points) :
    I.length ≤ J.length := by
  simpa only [integerInterval_card_points] using card_le_card h

theorem integerInterval_subset_equal_length {I J : SparseIntegerInterval}
    (h : I.points ⊆ J.points) (hlen : J.length ≤ I.length) : I = J := by
  have he := integerInterval_subset_length h
  have hb := (integerInterval_subset_iff I J).mp h
  have hl : I.left = J.left := by omega
  have hn : I.length = J.length := by omega
  cases I
  cases J
  simp_all

def SparseIntegerInterval.hull (I J : SparseIntegerInterval) : SparseIntegerInterval where
  left := min I.left J.left
  length := (max (I.left+I.length) (J.left+J.length) - min I.left J.left).toNat
  length_pos := by
    have := I.length_pos
    have hm := le_max_left (I.left+I.length) (J.left+J.length)
    have hn := min_le_left I.left J.left
    omega

theorem integerInterval_hull_mem (I J : SparseIntegerInterval) (x : ℤ) :
    x ∈ (I.hull J).points ↔
      min I.left J.left ≤ x ∧ x < max (I.left+I.length) (J.left+J.length) := by
  rw [integerInterval_mem_points]
  have hd : 0 ≤ max (I.left+I.length) (J.left+J.length) - min I.left J.left := by
    have := I.length_pos
    have hm := le_max_left (I.left+I.length) (J.left+J.length)
    have hn := min_le_left I.left J.left
    omega
  simp only [SparseIntegerInterval.hull, Int.toNat_of_nonneg hd]
  omega

theorem integerInterval_subset_hull_left (I J : SparseIntegerInterval) :
    I.points ⊆ (I.hull J).points := by
  intro x hx
  rw [integerInterval_mem_points] at hx
  rw [integerInterval_hull_mem]
  exact ⟨(min_le_left _ _).trans hx.1, hx.2.trans_le (le_max_left _ _)⟩

theorem integerInterval_subset_hull_right (I J : SparseIntegerInterval) :
    J.points ⊆ (I.hull J).points := by
  intro x hx
  rw [integerInterval_mem_points] at hx
  rw [integerInterval_hull_mem]
  exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans_le (le_max_right _ _)⟩

theorem integerInterval_hull_eq_union {I J : SparseIntegerInterval}
    (h : ¬ Disjoint I.points J.points) : (I.hull J).points = I.points ∪ J.points := by
  obtain ⟨z, hzI, hzJ⟩ := not_disjoint_iff.mp h
  rw [integerInterval_mem_points] at hzI hzJ
  ext x
  rw [integerInterval_hull_mem]
  simp only [mem_union, integerInterval_mem_points]
  omega

theorem integerInterval_five_subset {I J : SparseIntegerInterval} (h : I.points ⊆ J.points) :
    I.five.points ⊆ J.five.points := by
  have hb := (integerInterval_subset_iff I J).mp h
  have hn := integerInterval_subset_length h
  rw [integerInterval_subset_iff]
  simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> omega

end PrimeSquares
