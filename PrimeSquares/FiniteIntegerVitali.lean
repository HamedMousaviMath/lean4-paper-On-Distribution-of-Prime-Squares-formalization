import PrimeSquares.SparseIntegerIntervals

/-!
# A finite integer-interval covering argument

Select disjoint intervals in decreasing order of length. Every interval
meets a selected interval at least as long, and is covered by its triple.
This will give the counting-measure weak bound used in the stopping step.
-/

open Finset
namespace PrimeSquares

def SparseIntegerInterval.three (I : SparseIntegerInterval) : SparseIntegerInterval where
  left := I.left - (I.length : ℤ)
  length := 3 * I.length
  length_pos := Nat.mul_pos (by decide) I.length_pos

theorem integerInterval_intersect_subset_three {I J : SparseIntegerInterval}
    (h : ¬ Disjoint I.points J.points) (hlen : I.length ≤ J.length) :
    I.points ⊆ J.three.points := by
  obtain ⟨z, hzI, hzJ⟩ := not_disjoint_iff.mp h
  rw [integerInterval_mem_points] at hzI hzJ
  intro x hx
  rw [integerInterval_mem_points] at hx ⊢
  simp only [SparseIntegerInterval.three, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> omega

theorem finiteIntegerVitali (S : Finset SparseIntegerInterval) :
    ∃ U ⊆ S, (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points ∧
      ∀ I ∈ S, ∃ J ∈ U, ¬ Disjoint I.points J.points ∧ I.length ≤ J.length := by
  classical
  suffices ∀ n : ℕ, ∀ S : Finset SparseIntegerInterval, S.card = n →
    ∃ U ⊆ S, (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points ∧
      ∀ I ∈ S, ∃ J ∈ U, ¬ Disjoint I.points J.points ∧ I.length ≤ J.length by
    exact this S.card S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hSn
    by_cases hS : S = ∅
    · subst S
      exact ⟨∅, Subset.rfl, by simp, by simp⟩
    have hne := nonempty_iff_ne_empty.mpr hS
    obtain ⟨J, hJS, hmax⟩ := S.exists_max_image SparseIntegerInterval.length hne
    let T := S.filter (fun I => Disjoint I.points J.points)
    have hJnot : J ∉ T := by
      simp only [T, mem_filter, not_and]
      intro _ hd
      exact (integerInterval_nonempty_points J).ne_empty (disjoint_self.mp hd)
    have hT : T ⊆ S := filter_subset _ _
    have hcard : T.card < n := by
      rw [← hSn]
      exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hT, fun he => hJnot (he.symm ▸ hJS)⟩)
    obtain ⟨U, hUT, hUdisj, hcover⟩ := ih T.card hcard T rfl
    refine ⟨insert J U, ?_, ?_, ?_⟩
    · exact insert_subset hJS (hUT.trans hT)
    · intro A hA B hB hAB
      rcases mem_insert.mp hA with rfl | hAU
      · rcases mem_insert.mp hB with rfl | hBU
        · exact (hAB rfl).elim
        · exact ((mem_filter.mp (hUT hBU)).2).symm
      · rcases mem_insert.mp hB with rfl | hBU
        · exact (mem_filter.mp (hUT hAU)).2
        · exact hUdisj hAU hBU hAB
    · intro I hIS
      by_cases hd : Disjoint I.points J.points
      · obtain ⟨K, hKU, hIK, hlen⟩ := hcover I (mem_filter.mpr ⟨hIS, hd⟩)
        exact ⟨K, mem_insert_of_mem hKU, hIK, hlen⟩
      · exact ⟨J, mem_insert_self _ _, hd, hmax I hIS⟩

theorem finiteIntegerVitali_cover (S : Finset SparseIntegerInterval) :
    ∃ U ⊆ S, (U : Set SparseIntegerInterval).PairwiseDisjoint SparseIntegerInterval.points ∧
      S.biUnion SparseIntegerInterval.points ⊆
        U.biUnion (fun I => I.three.points) := by
  obtain ⟨U, hUS, hU, hcover⟩ := finiteIntegerVitali S
  refine ⟨U, hUS, hU, ?_⟩
  intro x hx
  obtain ⟨I, hIS, hxI⟩ := mem_biUnion.mp hx
  obtain ⟨J, hJU, hIJ, hlen⟩ := hcover I hIS
  exact mem_biUnion.mpr ⟨J, hJU, integerInterval_intersect_subset_three hIJ hlen hxI⟩

end PrimeSquares
