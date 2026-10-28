import PrimeSquares.IntegerIntervalGeometry

/-! # The finite collection of all nonempty subintervals of an integer interval -/

open Finset
namespace PrimeSquares

def integerSubintervals (R : SparseIntegerInterval) : Finset SparseIntegerInterval :=
  ((R.points ×ˢ Icc 1 R.length).image (fun p : ℤ × ℕ =>
    ({left := p.1, length := max p.2 1,
      length_pos := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)} : SparseIntegerInterval))).filter
    (fun I => I.left + I.length ≤ R.left + R.length)

theorem mem_integerSubintervals (R I : SparseIntegerInterval) :
    I ∈ integerSubintervals R ↔ I.points ⊆ R.points := by
  constructor
  · intro h
    obtain ⟨hi, hr⟩ := mem_filter.mp h
    obtain ⟨p, hp, he⟩ := mem_image.mp hi
    have hleft : p.1 ∈ R.points := (mem_product.mp hp).1
    have hla : R.left ≤ I.left := by
      have hl := (integerInterval_mem_points R p.1).mp hleft
      have hh := congrArg SparseIntegerInterval.left he
      simpa only using hl.1.trans_eq hh
    exact (integerInterval_subset_iff I R).mpr ⟨hla, hr⟩
  · intro h
    have hlen := integerInterval_subset_length h
    have hpos := I.length_pos
    have hleft := h (integerInterval_left_mem I)
    have hright := ((integerInterval_subset_iff I R).mp h).2
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨(I.left, I.length), mem_product.mpr
      ⟨hleft, mem_Icc.mpr ⟨by omega, hlen⟩⟩, ?_⟩, hright⟩
    have hm : max I.length 1 = I.length := max_eq_left (by omega)
    cases I with
    | mk a n hn =>
      dsimp only at hm ⊢
      simp only [hm]

theorem integerSubintervals_self (R : SparseIntegerInterval) : R ∈ integerSubintervals R :=
  (mem_integerSubintervals R R).mpr Subset.rfl

theorem integerSubintervals_trans {R I J : SparseIntegerInterval}
    (hI : I ∈ integerSubintervals R) (hJ : J ∈ integerSubintervals I) :
    J ∈ integerSubintervals R :=
  (mem_integerSubintervals R J).mpr (((mem_integerSubintervals I J).mp hJ).trans
    ((mem_integerSubintervals R I).mp hI))

def integerSingletonInterval (x : ℤ) : SparseIntegerInterval where
  left := x
  length := 1
  length_pos := by decide

theorem integerSingletonInterval_points (x : ℤ) : (integerSingletonInterval x).points = {x} := by
  ext y
  simp only [integerInterval_mem_points, integerSingletonInterval, Nat.cast_one, mem_singleton]
  omega

def integerComponentCandidates (R : SparseIntegerInterval) (B : Finset ℤ) :
    Finset SparseIntegerInterval := (integerSubintervals R).filter (fun I => I.points ⊆ B)

def integerMaximalComponents (R : SparseIntegerInterval) (B : Finset ℤ) :
    Finset SparseIntegerInterval :=
  (integerComponentCandidates R B).filter (fun I =>
    ∀ J ∈ integerComponentCandidates R B, I.points ⊆ J.points → J.length ≤ I.length)

theorem integerMaximalComponents_subset {R : SparseIntegerInterval} {B : Finset ℤ}
    {I : SparseIntegerInterval} (h : I ∈ integerMaximalComponents R B) :
    I.points ⊆ R.points ∧ I.points ⊆ B := by
  have hh := mem_filter.mp ((mem_filter.mp h).1)
  exact ⟨(mem_integerSubintervals R I).mp hh.1, hh.2⟩

theorem integerMaximalComponents_cover {R : SparseIntegerInterval} {B : Finset ℤ}
    (hB : B ⊆ R.points) : (integerMaximalComponents R B).biUnion
      SparseIntegerInterval.points = B := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨I, hI, hxI⟩ := mem_biUnion.mp hx
    exact (integerMaximalComponents_subset hI).2 hxI
  · intro x hx
    let T := (integerComponentCandidates R B).filter (fun I => x ∈ I.points)
    have hs : integerSingletonInterval x ∈ T := by
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨(mem_integerSubintervals R _).mpr ?_, ?_⟩, ?_⟩
      · rw [integerSingletonInterval_points]
        exact singleton_subset_iff.mpr (hB hx)
      · rw [integerSingletonInterval_points]
        exact singleton_subset_iff.mpr hx
      · rw [integerSingletonInterval_points]
        exact mem_singleton_self _
    obtain ⟨I, hIT, hmax⟩ := T.exists_max_image SparseIntegerInterval.length ⟨_, hs⟩
    obtain ⟨hI, hxI⟩ := mem_filter.mp hIT
    apply mem_biUnion.mpr
    refine ⟨I, mem_filter.mpr ⟨hI, ?_⟩, hxI⟩
    intro J hJ hIJ
    exact hmax J (mem_filter.mpr ⟨hJ, hIJ hxI⟩)

theorem integerMaximalComponents_disjoint (R : SparseIntegerInterval) (B : Finset ℤ) :
    (integerMaximalComponents R B : Set SparseIntegerInterval).PairwiseDisjoint
      SparseIntegerInterval.points := by
  intro I hI J hJ hne
  by_contra hd
  have hIJ := integerInterval_hull_eq_union hd
  have hI' := integerMaximalComponents_subset hI
  have hJ' := integerMaximalComponents_subset hJ
  have hHull : I.hull J ∈ integerComponentCandidates R B := by
    apply mem_filter.mpr
    rw [mem_integerSubintervals, hIJ]
    exact ⟨union_subset hI'.1 hJ'.1, union_subset hI'.2 hJ'.2⟩
  have hi := (mem_filter.mp hI).2 _ hHull (integerInterval_subset_hull_left I J)
  have hj := (mem_filter.mp hJ).2 _ hHull (integerInterval_subset_hull_right I J)
  exact hne ((integerInterval_subset_equal_length (integerInterval_subset_hull_left I J) hi).trans
    (integerInterval_subset_equal_length (integerInterval_subset_hull_right I J) hj).symm)

end PrimeSquares
