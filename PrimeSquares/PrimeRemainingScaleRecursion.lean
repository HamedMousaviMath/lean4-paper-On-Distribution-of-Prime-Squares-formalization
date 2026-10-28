import PrimeSquares.FiniteAnnularMaximum
import PrimeSquares.PrimeStoppingGeometry
import PrimeSquares.AnnularStoppingSupport

/-! # The exact one-generation decomposition of the actual finite maximum -/

open Finset
open scoped NNReal
namespace PrimeSquares

noncomputable def primeRemainingIndices (I : SparseIntegerInterval) (F : Finset ℤ) (x : ℤ) :
    Finset ℕ := (dyadicSpatialIndices I.length).filter (fun j =>
      ∀ A ∈ primeStoppingChildren I (F ∩ I.five.points), x ∈ A.points →
        A.length < ((2 : ℕ)^j*2)^2)

theorem primeRemainingIndices_subset (I : SparseIntegerInterval) (F : Finset ℤ) (x : ℤ) :
    primeRemainingIndices I F x ⊆ dyadicSpatialIndices I.length := filter_subset _ _

theorem primeRemainingScale_admissible (I : SparseIntegerInterval) (F : Finset ℤ) {x : ℤ}
    (hx : x ∈ I.points) {j : ℕ} (hj : j ∈ primeRemainingIndices I F x) :
    sourceLocalMass ((2 : ℕ)^j*2) (finiteIndicatorLp (F ∩ I.five.points) 1) x ≤
      320 * (((F ∩ I.five.points).card : ℝ) / I.length) := by
  apply primeStopping_remaining_localMass I (F ∩ I.five.points)
    (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) hx
  exact (mem_filter.mp hj).2

theorem primeRemainingScale_pointwise (I : SparseIntegerInterval) (F : Finset ℤ) {x : ℤ}
    (_hx : x ∈ I.points) :
    truncatedAnnularMaximum I.length (F ∩ I.five.points) x ≤
      finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x +
      ∑ A ∈ primeStoppingChildren I (F ∩ I.five.points),
        if x ∈ A.points then truncatedAnnularMaximum A.length (F ∩ A.five.points) x else 0 := by
  unfold truncatedAnnularMaximum finiteAnnularMaximum
  apply Finset.sup_le
  intro j hj
  by_cases hr : j ∈ primeRemainingIndices I F x
  · exact (Finset.le_sup (f := fun j => ‖annularDyadicValue j (F ∩ I.five.points) x‖₊) hr).trans
      (le_add_of_nonneg_right (by positivity))
  · have hnorem : ¬ ∀ A ∈ primeStoppingChildren I (F ∩ I.five.points), x ∈ A.points →
        A.length < ((2 : ℕ)^j*2)^2 := by
      intro h
      exact hr (mem_filter.mpr ⟨hj, h⟩)
    push Not at hnorem
    obtain ⟨A, hA, hxA, hN⟩ := hnorem
    have hAI := (primeStoppingChildren_geometry hA).1
    have hv : annularDyadicValue j (F ∩ I.five.points) x =
        annularDyadicValue j (F ∩ A.five.points) x :=
      annularSquare_indicator_restrict_twice hAI hN _ F hxA
    have hja := (mem_dyadicSpatialIndices A.length j).mpr hN
    have hmax := Finset.le_sup (f := fun j => ‖annularDyadicValue j (F ∩ A.five.points) x‖₊) hja
    have hsingle := Finset.single_le_sum (s := primeStoppingChildren I (F ∩ I.five.points))
      (f := fun B => if x ∈ B.points then
        (dyadicSpatialIndices B.length).sup (fun j => ‖annularDyadicValue j (F ∩ B.five.points) x‖₊)
        else 0) (fun _ _ => by positivity) hA
    rw [ite_eq_left hxA] at hsingle
    rw [hv]
    exact (hmax.trans hsingle).trans (le_add_of_nonneg_left (by positivity))

theorem finiteSum_interval_mask (I A : SparseIntegerInterval) (hA : A.points ⊆ I.points)
    (G : Finset ℤ) (v : ℤ → ℝ) :
    (∑ x ∈ G ∩ I.points, if x ∈ A.points then v x else 0) = ∑ x ∈ G ∩ A.points, v x := by
  rw [← sum_filter]
  apply sum_congr
  · ext x
    simp only [mem_filter, mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hA h.2⟩, h.2⟩⟩
  · intro _ _
    rfl

theorem primeRemainingScale_pairing (I : SparseIntegerInterval) (F G : Finset ℤ) :
    annularLocalMaxPairing I F G ≤
      (∑ x ∈ G ∩ I.points,
        (finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x : ℝ)) +
      ∑ A ∈ primeStoppingChildren I (F ∩ I.five.points), annularLocalMaxPairing A F G := by
  have h := sum_le_sum (fun x (hx : x ∈ G ∩ I.points) =>
    show (truncatedAnnularMaximum I.length (F ∩ I.five.points) x : ℝ) ≤ _ from
      (NNReal.coe_le_coe.mpr (primeRemainingScale_pointwise I F (mem_inter.mp hx).2)))
  simp only [NNReal.coe_add, NNReal.coe_sum, apply_ite, NNReal.coe_zero] at h
  rw [sum_add_distrib, sum_comm] at h
  exact h.trans_eq (congrArg ((∑ x ∈ G ∩ I.points,
      (finiteAnnularMaximum (primeRemainingIndices I F x) (F ∩ I.five.points) x : ℝ)) + ·)
    (sum_congr rfl (fun A hA => finiteSum_interval_mask I A
      (primeStoppingChildren_geometry hA).1 G _)))

end PrimeSquares
