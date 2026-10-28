import PrimeSquares.FiniteSparseRecursion

/-!
# Sparse recursion without an ambient dyadic-grid hypothesis

Disjoint children generate a laminar output even when the ambient set
contains every subinterval. This allows a finite stopping proof using
maximal consecutive bad intervals.
-/

open Finset
namespace PrimeSquares

theorem integerLaminar_glue (R : SparseIntegerInterval)
    (U : Finset SparseIntegerInterval) (SU : SparseIntegerInterval → Finset SparseIntegerInterval)
    (hU : (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points)
    (hlen : ∀ A ∈ U, A.points ⊆ R.points ∧ A.length < R.length)
    (hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length)
    (hinner : ∀ A ∈ U, IntegerLaminar (SU A)) :
    IntegerLaminar (insert R (U.biUnion SU)) := by
  intro I hI J hJ hne
  rcases mem_insert.mp hI with hIR | hIU
  · subst I
    rcases mem_insert.mp hJ with hJR | hJU
    · exact (hne hJR.symm).elim
    · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hJU
      exact Or.inr (Or.inr ⟨((hsub A hA J hJA).1).trans (hlen A hA).1,
        ((hsub A hA J hJA).2).trans_lt (hlen A hA).2⟩)
  · obtain ⟨A, hA, hIA⟩ := mem_biUnion.mp hIU
    rcases mem_insert.mp hJ with hJR | hJU
    · subst J
      exact Or.inr (Or.inl ⟨((hsub A hA I hIA).1).trans (hlen A hA).1,
        ((hsub A hA I hIA).2).trans_lt (hlen A hA).2⟩)
    · obtain ⟨B, hB, hJB⟩ := mem_biUnion.mp hJU
      by_cases hab : A = B
      · subst B
        exact hinner A hA I hIA J hJB hne
      · exact Or.inl ((hU hA hB hab).mono (hsub A hA I hIA).1 (hsub B hB J hJB).1)

theorem laminarSparseRecursion_certificate (D : Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ)
    (hstep : ∀ I ∈ D, IntegerSparseStep D V b I) (R : SparseIntegerInterval) (hR : R ∈ D) :
    ∃ S ⊆ D, IntegerLaminar S ∧ R ∈ S ∧
      (∀ J ∈ S, J.points ⊆ R.points ∧ J.length ≤ R.length) ∧
      (∀ J ∈ S, ((integerDescendantUnion S J).card : ℝ) ≤ (J.length : ℝ)/4) ∧
      V R ≤ ∑ J ∈ S, b J := by
  classical
  suffices ∀ n : ℕ, ∀ R : SparseIntegerInterval, R.length = n → R ∈ D →
    ∃ S ⊆ D, IntegerLaminar S ∧ R ∈ S ∧
      (∀ J ∈ S, J.points ⊆ R.points ∧ J.length ≤ R.length) ∧
      (∀ J ∈ S, ((integerDescendantUnion S J).card : ℝ) ≤ (J.length : ℝ)/4) ∧
      V R ≤ ∑ J ∈ S, b J by
    exact this R.length R rfl hR
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R hRn hRD
    obtain ⟨U, hUD, hUR, hU, hpack, hrec⟩ := hstep R hRD
    have hchild : ∀ A : SparseIntegerInterval, ∃ S : Finset SparseIntegerInterval,
        A ∈ U → S ⊆ D ∧ IntegerLaminar S ∧ A ∈ S ∧
          (∀ J ∈ S, J.points ⊆ A.points ∧ J.length ≤ A.length) ∧
          (∀ J ∈ S, ((integerDescendantUnion S J).card : ℝ) ≤ (J.length : ℝ)/4) ∧
          V A ≤ ∑ J ∈ S, b J := by
      intro A
      by_cases hA : A ∈ U
      · obtain ⟨S, hSD, hSL, hAS, hs, hp, hc⟩ := ih A.length
          (by have := (hUR A hA).2; omega) A rfl (hUD hA)
        exact ⟨S, fun _ => ⟨hSD, hSL, hAS, hs, hp, hc⟩⟩
      · exact ⟨∅, fun h => (hA h).elim⟩
    choose SU hSU using hchild
    let S := insert R (U.biUnion SU)
    have hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length :=
      fun A hA => (hSU A hA).2.2.2.1
    refine ⟨S, ?_, ?_, mem_insert_self _ _, ?_, ?_, ?_⟩
    · intro J hJ
      rcases mem_insert.mp hJ with he | hj
      · exact he ▸ hRD
      · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hj
        exact (hSU A hA).1 hJA
    · exact integerLaminar_glue R U SU hU hUR hsub (fun A hA => (hSU A hA).2.1)
    · intro J hJ
      rcases mem_insert.mp hJ with he | hj
      · subst J
        exact ⟨Subset.rfl, le_rfl⟩
      · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hj
        exact ⟨((hsub A hA J hJA).1).trans (hUR A hA).1,
          ((hsub A hA J hJA).2).trans (hUR A hA).2.le⟩
    · exact integerSparse_glue_packing R U SU hU (fun A hA => (hUR A hA).2)
        hsub hpack (fun A hA => (hSU A hA).2.2.2.2.1)
    · exact integerSparse_glue_cost R U SU V b hU (fun A hA => (hUR A hA).2)
        hsub hrec (fun A hA => (hSU A hA).2.2.2.2.2)

theorem laminarSparseRecursion (D : Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ)
    (hstep : ∀ I ∈ D, IntegerSparseStep D V b I) (R : SparseIntegerInterval) (hR : R ∈ D) :
    ∃ S ⊆ D, IntegerSparseFamily (3/4) S ∧ V R ≤ ∑ I ∈ S, b I := by
  obtain ⟨S, hSD, hSL, _, _, hpack, hcost⟩ :=
    laminarSparseRecursion_certificate D V b hstep R hR
  refine ⟨S, hSD, integerSparseFamily_of_laminar hSL ?_, hcost⟩
  intro I hI
  have h := hpack I hI
  nlinarith

end PrimeSquares
