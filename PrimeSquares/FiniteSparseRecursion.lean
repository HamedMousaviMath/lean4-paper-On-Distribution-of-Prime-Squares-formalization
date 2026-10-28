import PrimeSquares.FiniteSparseGluing

/-!
# Finite stopping recursion implies a genuine sparse bound

Every recursive call has strictly shorter integer length, so the iteration
terminates. The output contains actual intervals and disjoint major sets.
The one-generation inequality remains a theorem hypothesis here; supplying
it for the actual averages is the subsequent analytic and geometric work.
-/

open Finset
namespace PrimeSquares

def IntegerSparseStep (D : Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ) (I : SparseIntegerInterval) : Prop :=
  ∃ U ⊆ D,
    (∀ A ∈ U, A.points ⊆ I.points ∧ A.length < I.length) ∧
    (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points ∧
    ((U.biUnion SparseIntegerInterval.points).card : ℝ) ≤ (I.length : ℝ)/4 ∧
    V I ≤ b I + ∑ A ∈ U, V A

theorem integerLaminar_subset {S D : Finset SparseIntegerInterval}
    (hD : IntegerLaminar D) (hS : S ⊆ D) : IntegerLaminar S := by
  intro I hI J hJ hne
  exact hD I (hS hI) J (hS hJ) hne

theorem finiteSparseRecursion_certificate (D : Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ)
    (hstep : ∀ I ∈ D, IntegerSparseStep D V b I) (R : SparseIntegerInterval) (hR : R ∈ D) :
    ∃ S ⊆ D, R ∈ S ∧
      (∀ J ∈ S, J.points ⊆ R.points ∧ J.length ≤ R.length) ∧
      (∀ J ∈ S, ((integerDescendantUnion S J).card : ℝ) ≤ (J.length : ℝ)/4) ∧
      V R ≤ ∑ J ∈ S, b J := by
  classical
  suffices ∀ n : ℕ, ∀ R : SparseIntegerInterval, R.length = n → R ∈ D →
    ∃ S ⊆ D, R ∈ S ∧
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
        A ∈ U → S ⊆ D ∧ A ∈ S ∧
          (∀ J ∈ S, J.points ⊆ A.points ∧ J.length ≤ A.length) ∧
          (∀ J ∈ S, ((integerDescendantUnion S J).card : ℝ) ≤ (J.length : ℝ)/4) ∧
          V A ≤ ∑ J ∈ S, b J := by
      intro A
      by_cases hA : A ∈ U
      · obtain ⟨S, hSD, hAS, hs, hp, hc⟩ := ih A.length
          (by have := (hUR A hA).2; omega) A rfl (hUD hA)
        exact ⟨S, fun _ => ⟨hSD, hAS, hs, hp, hc⟩⟩
      · exact ⟨∅, fun h => (hA h).elim⟩
    choose SU hSU using hchild
    let S := insert R (U.biUnion SU)
    have hsub : ∀ A ∈ U, ∀ J ∈ SU A, J.points ⊆ A.points ∧ J.length ≤ A.length :=
      fun A hA => (hSU A hA).2.2.1
    refine ⟨S, ?_, mem_insert_self _ _, ?_, ?_, ?_⟩
    · intro J hJ
      rcases mem_insert.mp hJ with he | hj
      · exact he ▸ hRD
      · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hj
        exact (hSU A hA).1 hJA
    · intro J hJ
      rcases mem_insert.mp hJ with he | hj
      · subst J
        exact ⟨Subset.rfl, le_rfl⟩
      · obtain ⟨A, hA, hJA⟩ := mem_biUnion.mp hj
        exact ⟨((hsub A hA J hJA).1).trans (hUR A hA).1,
          ((hsub A hA J hJA).2).trans (hUR A hA).2.le⟩
    · exact integerSparse_glue_packing R U SU hU (fun A hA => (hUR A hA).2)
        hsub hpack (fun A hA => (hSU A hA).2.2.2.1)
    · exact integerSparse_glue_cost R U SU V b hU (fun A hA => (hUR A hA).2)
        hsub hrec (fun A hA => (hSU A hA).2.2.2.2)

theorem finiteSparseRecursion (D : Finset SparseIntegerInterval)
    (V b : SparseIntegerInterval → ℝ) (hD : IntegerLaminar D)
    (hstep : ∀ I ∈ D, IntegerSparseStep D V b I) (R : SparseIntegerInterval) (hR : R ∈ D) :
    ∃ S ⊆ D, IntegerSparseFamily (3/4) S ∧ V R ≤ ∑ I ∈ S, b I := by
  obtain ⟨S, hSD, _, _, hpack, hcost⟩ :=
    finiteSparseRecursion_certificate D V b hstep R hR
  refine ⟨S, hSD, integerSparseFamily_of_laminar (integerLaminar_subset hD hSD) ?_, hcost⟩
  intro I hI
  have h := hpack I hI
  nlinarith

end PrimeSquares
