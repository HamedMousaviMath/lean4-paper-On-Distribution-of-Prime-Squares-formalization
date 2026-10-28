import PrimeSquares.FiniteSparseMajorSets

/-!
# Gluing finite sparse interval constructions below disjoint children

The hypotheses are a single stopping generation and certificates already
proved below its children. The conclusion proves actual descendant packing
and an exact recursive cost bound for their union.
-/

open Finset
namespace PrimeSquares

theorem intervalSubfamilies_disjoint (U : Finset SparseIntegerInterval)
    (SU : SparseIntegerInterval → Finset SparseIntegerInterval)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points) :
    (U : Set SparseIntegerInterval).PairwiseDisjoint SU := by
  intro A hA B hB hne
  apply disjoint_left.mpr
  intro J hJA hJB
  obtain ⟨x, hx⟩ := integerInterval_nonempty_points J
  exact disjoint_left.mp (hU hA hB hne) (hsub A hA J hJA hx) (hsub B hB J hJB hx)

theorem integerDescendantUnion_glue_subset (R : SparseIntegerInterval)
    (U : Finset SparseIntegerInterval) (SU : SparseIntegerInterval → Finset SparseIntegerInterval)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (hlen : ∀ A ∈ U, A.length < R.length)
    (hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length)
    {A J : SparseIntegerInterval} (hA : A ∈ U) (hJ : J ∈ SU A) :
    integerDescendantUnion (insert R (U.biUnion SU)) J ⊆ integerDescendantUnion (SU A) J := by
  intro x hx
  obtain ⟨K, hKS, hxK⟩ := mem_biUnion.mp hx
  obtain ⟨hK, hKlen, hKJ⟩ := mem_filter.mp hKS
  have hKR : K ≠ R := by
    intro he
    subst K
    have hJA := (hsub A hA J hJ).2
    have hAR := hlen A hA
    omega
  have hKU : K ∈ U.biUnion SU := (mem_insert.mp hK).resolve_left hKR
  obtain ⟨B, hB, hKB⟩ := mem_biUnion.mp hKU
  have hBA : B = A := by
    by_contra hne
    have hxB := (hsub B hB K hKB).1 hxK
    have hxA := (hsub A hA J hJ).1 (hKJ hxK)
    exact disjoint_left.mp (hU hB hA hne) hxB hxA
  subst B
  exact mem_biUnion.mpr ⟨K, mem_filter.mpr ⟨hKB, hKlen, hKJ⟩, hxK⟩

theorem integerSparse_glue_packing (R : SparseIntegerInterval)
    (U : Finset SparseIntegerInterval) (SU : SparseIntegerInterval → Finset SparseIntegerInterval)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (hlen : ∀ A ∈ U, A.length < R.length)
    (hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length)
    (hpack : ((U.biUnion SparseIntegerInterval.points).card : ℝ) ≤ (R.length : ℝ)/4)
    (hinner : ∀ A ∈ U, ∀ J ∈ SU A,
      ((integerDescendantUnion (SU A) J).card : ℝ) ≤ (J.length : ℝ)/4) :
    ∀ J ∈ insert R (U.biUnion SU),
      ((integerDescendantUnion (insert R (U.biUnion SU)) J).card : ℝ) ≤ (J.length : ℝ)/4 := by
  intro J hJ
  rcases mem_insert.mp hJ with hJR | hJU
  · subst J
    have hcover : integerDescendantUnion (insert R (U.biUnion SU)) R ⊆
        U.biUnion SparseIntegerInterval.points := by
      intro x hx
      obtain ⟨K, hKS, hxK⟩ := mem_biUnion.mp hx
      obtain ⟨hK, hKlen, _⟩ := mem_filter.mp hKS
      have hKR : K ≠ R := by intro he; subst K; omega
      obtain ⟨A, hA, hKA⟩ := mem_biUnion.mp ((mem_insert.mp hK).resolve_left hKR)
      exact mem_biUnion.mpr ⟨A, hA, (hsub A hA K hKA).1 hxK⟩
    have hc : ((integerDescendantUnion (insert R (U.biUnion SU)) R).card : ℝ) ≤
        (U.biUnion SparseIntegerInterval.points).card := by exact_mod_cast card_le_card hcover
    exact hc.trans hpack
  · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hJU
    have hc : ((integerDescendantUnion (insert R (U.biUnion SU)) J).card : ℝ) ≤
        (integerDescendantUnion (SU A) J).card := by
      exact_mod_cast card_le_card (integerDescendantUnion_glue_subset R U SU hU hlen hsub hA hJA)
    exact hc.trans (hinner A hA J hJA)

theorem integerSparse_glue_cost (R : SparseIntegerInterval)
    (U : Finset SparseIntegerInterval) (SU : SparseIntegerInterval → Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (hlen : ∀ A ∈ U, A.length < R.length)
    (hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length)
    (hstep : V R ≤ b R + ∑ A ∈ U, V A)
    (hinner : ∀ A ∈ U, V A ≤ ∑ J ∈ SU A, b J) :
    V R ≤ ∑ J ∈ insert R (U.biUnion SU), b J := by
  have hR : R ∉ U.biUnion SU := by
    intro h
    obtain ⟨A, hA, hRA⟩ := mem_biUnion.mp h
    have hle := (hsub A hA R hRA).2
    have hlt := hlen A hA
    omega
  rw [sum_insert hR, sum_biUnion (intervalSubfamilies_disjoint U SU hU
    (fun A hA J hJ => (hsub A hA J hJ).1))]
  exact hstep.trans (add_le_add_right (sum_le_sum hinner) _)

end PrimeSquares
