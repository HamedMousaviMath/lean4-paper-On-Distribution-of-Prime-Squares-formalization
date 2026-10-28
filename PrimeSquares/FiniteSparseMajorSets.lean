import PrimeSquares.SparseIntegerIntervals

/-!
# Actual major subsets of finite laminar interval families

Deleting the strict descendants gives disjoint major subsets. Fivefold
dilation retains those same subsets, with the exact division of sparsity
by five. No dyadic-grid replacement or unstated sparsity convention is used.
-/

open Finset
namespace PrimeSquares

instance : Nonempty SparseIntegerInterval := ⟨⟨0, 1, by decide⟩⟩

def IntegerLaminar (S : Finset SparseIntegerInterval) : Prop :=
  ∀ I ∈ S, ∀ J ∈ S, I ≠ J →
    Disjoint I.points J.points ∨
    (I.points ⊆ J.points ∧ I.length < J.length) ∨
    (J.points ⊆ I.points ∧ J.length < I.length)

def integerDescendantUnion (S : Finset SparseIntegerInterval) (I : SparseIntegerInterval) :
    Finset ℤ := (S.filter (fun J => J.length < I.length ∧ J.points ⊆ I.points)).biUnion
      SparseIntegerInterval.points

def integerMajorCore (S : Finset SparseIntegerInterval) (I : SparseIntegerInterval) :
    Finset ℤ := I.points \ integerDescendantUnion S I

theorem integerMajorCore_subset (S : Finset SparseIntegerInterval) (I : SparseIntegerInterval) :
    integerMajorCore S I ⊆ I.points := sdiff_subset

theorem integerMajorCore_disjoint_descendant {S : Finset SparseIntegerInterval}
    {I J : SparseIntegerInterval} (hJ : J ∈ S) (hlen : J.length < I.length)
    (hJI : J.points ⊆ I.points) : Disjoint (integerMajorCore S I) J.points := by
  apply disjoint_left.mpr
  intro x hx hJx
  have hU : x ∈ integerDescendantUnion S I := mem_biUnion.mpr
    ⟨J, mem_filter.mpr ⟨hJ, hlen, hJI⟩, hJx⟩
  exact (mem_sdiff.mp hx).2 hU

theorem integerMajorCore_pairwise {S : Finset SparseIntegerInterval} (hS : IntegerLaminar S) :
    (S : Set SparseIntegerInterval).PairwiseDisjoint (integerMajorCore S) := by
  intro I hI J hJ hne
  rcases hS I hI J hJ hne with hd | hIJ | hJI
  · exact hd.mono (integerMajorCore_subset S I) (integerMajorCore_subset S J)
  · exact (integerMajorCore_disjoint_descendant hI hIJ.2 hIJ.1).symm.mono_left
      (integerMajorCore_subset S I)
  · exact (integerMajorCore_disjoint_descendant hJ hJI.2 hJI.1).mono_right
      (integerMajorCore_subset S J)

theorem integerMajorCore_card {S : Finset SparseIntegerInterval} {I : SparseIntegerInterval}
    {η : ℝ} (hpack : ((integerDescendantUnion S I).card : ℝ) ≤ (1-η)*(I.length : ℝ)) :
    η * (I.length : ℝ) ≤ (integerMajorCore S I).card := by
  have h := card_sdiff_add_card_inter I.points (integerDescendantUnion S I)
  have hi := card_le_card (inter_subset_right : I.points ∩ integerDescendantUnion S I ⊆ _)
  have hr : ((integerMajorCore S I).card : ℝ) +
      ((I.points ∩ integerDescendantUnion S I).card : ℝ) = I.length := by
    exact_mod_cast h.trans (integerInterval_card_points I)
  have hir : ((I.points ∩ integerDescendantUnion S I).card : ℝ) ≤
      (integerDescendantUnion S I).card := by exact_mod_cast hi
  nlinarith

theorem integerSparseFamily_of_laminar {S : Finset SparseIntegerInterval} {η : ℝ}
    (hlam : IntegerLaminar S)
    (hpack : ∀ I ∈ S, ((integerDescendantUnion S I).card : ℝ) ≤ (1-η)*(I.length : ℝ)) :
    IntegerSparseFamily η S := by
  exact ⟨integerMajorCore S, fun I hI =>
    ⟨integerMajorCore_subset S I, integerMajorCore_card (hpack I hI)⟩,
    integerMajorCore_pairwise hlam⟩

theorem integerSparseFamily_five {S : Finset SparseIntegerInterval} {η : ℝ}
    (hS : IntegerSparseFamily η S) :
    IntegerSparseFamily (η/5) (S.image SparseIntegerInterval.five) := by
  classical
  obtain ⟨E, hE, hd⟩ := hS
  let E' := fun I => E (Function.invFun SparseIntegerInterval.five I)
  have hinv := Function.leftInverse_invFun integerInterval_five_injective
  refine ⟨E', ?_, ?_⟩
  · intro J hJ
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hJ
    have he : E' I.five = E I := congrArg E (hinv I)
    rw [he]
    refine ⟨(hE I hI).1.trans (integerInterval_points_subset_five I), ?_⟩
    have ht : (η/5) * (I.five.length : ℝ) = η * (I.length : ℝ) := by
      simp only [SparseIntegerInterval.five, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [ht]
    exact (hE I hI).2
  · intro I hI J hJ hne
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hI
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hJ
    have hab : A ≠ B := fun h => hne (congrArg SparseIntegerInterval.five h)
    change Disjoint (E (Function.invFun SparseIntegerInterval.five A.five))
      (E (Function.invFun SparseIntegerInterval.five B.five))
    rw [hinv A, hinv B]
    exact hd hA hB hab

theorem integerSparseFamily_five_source {S : Finset SparseIntegerInterval}
    (hS : IntegerSparseFamily (3/4) S) :
    IntegerSparseFamily (1/10) (S.image SparseIntegerInterval.five) := by
  exact integerSparseFamily_mono (integerSparseFamily_five hS) (by norm_num)

end PrimeSquares
