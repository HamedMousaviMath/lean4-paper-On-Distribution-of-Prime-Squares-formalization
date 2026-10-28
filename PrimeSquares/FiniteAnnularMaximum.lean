import PrimeSquares.IntegerIntervalGeometry
import PrimeSquares.PrimeSquareAverages

/-! # Actual finite dyadic prime-square maxima at spatial scale N squared -/

open Finset
open scoped NNReal
namespace PrimeSquares

def dyadicSpatialIndices (L : ℕ) : Finset ℕ :=
  (range L).filter (fun j => ((2 : ℕ)^j*2)^2 ≤ L)

theorem mem_dyadicSpatialIndices (L j : ℕ) :
    j ∈ dyadicSpatialIndices L ↔ ((2 : ℕ)^j*2)^2 ≤ L := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    have hj : j < (2 : ℕ)^j := Nat.lt_two_pow_self
    have hn : (2 : ℕ)^j ≤ (2 : ℕ)^j*2 := by omega
    have hp : 0 < (2 : ℕ)^j*2 := by positivity
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, h⟩
    nlinarith

theorem dyadicSpatialIndices_mono {L M : ℕ} (hLM : L ≤ M) :
    dyadicSpatialIndices L ⊆ dyadicSpatialIndices M := by
  intro j hj
  exact (mem_dyadicSpatialIndices M j).mpr (((mem_dyadicSpatialIndices L j).mp hj).trans hLM)

theorem dyadicSpatialIndices_empty {L : ℕ} (hL : L < 4) : dyadicSpatialIndices L = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := (mem_dyadicSpatialIndices L j).mp hj
  have hn : 2 ≤ (2 : ℕ)^j*2 := by
    have hp : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by decide)
    omega
  nlinarith

noncomputable def annularDyadicValue (j : ℕ) (F : Finset ℤ) (x : ℤ) : ℂ :=
  indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^j*2)
    ArithmeticFunction.vonMangoldt) F x

noncomputable def finiteAnnularMaximum (J : Finset ℕ) (F : Finset ℤ) (x : ℤ) : ℝ≥0 :=
  J.sup (fun j => ‖annularDyadicValue j F x‖₊)

noncomputable def truncatedAnnularMaximum (L : ℕ) (F : Finset ℤ) (x : ℤ) : ℝ≥0 :=
  finiteAnnularMaximum (dyadicSpatialIndices L) F x

noncomputable def annularLocalMaxPairing (I : SparseIntegerInterval) (F G : Finset ℤ) : ℝ :=
  ∑ x ∈ G ∩ I.points, (truncatedAnnularMaximum I.length (F ∩ I.five.points) x : ℝ)

theorem finiteAnnularMaximum_dominates (J : Finset ℕ) (F : Finset ℤ) (x : ℤ)
    {j : ℕ} (hj : j ∈ J) : ‖annularDyadicValue j F x‖₊ ≤ finiteAnnularMaximum J F x :=
  Finset.le_sup (f := fun j => ‖annularDyadicValue j F x‖₊) hj

theorem finiteAnnularMaximum_mono {J K : Finset ℕ} (hJK : J ⊆ K) (F : Finset ℤ) (x : ℤ) :
    finiteAnnularMaximum J F x ≤ finiteAnnularMaximum K F x := by
  unfold finiteAnnularMaximum
  apply Finset.sup_le
  intro j hj
  exact Finset.le_sup (f := fun j => ‖annularDyadicValue j F x‖₊) (hJK hj)

theorem finiteAnnularMaximum_attained {J : Finset ℕ} (hJ : J.Nonempty)
    (F : Finset ℤ) (x : ℤ) :
    ∃ j ∈ J, finiteAnnularMaximum J F x = ‖annularDyadicValue j F x‖₊ :=
  exists_mem_eq_sup J hJ _

theorem finiteAnnularMaximum_le {J : Finset ℕ} (F : Finset ℤ) (x : ℤ) {B : ℝ≥0}
    (hB : ∀ j ∈ J, ‖annularDyadicValue j F x‖₊ ≤ B) : finiteAnnularMaximum J F x ≤ B :=
  Finset.sup_le hB

theorem finiteAnnularMaximum_union (J K : Finset ℕ) (F : Finset ℤ) (x : ℤ) :
    finiteAnnularMaximum (J ∪ K) F x ≤ finiteAnnularMaximum J F x + finiteAnnularMaximum K F x := by
  unfold finiteAnnularMaximum
  apply Finset.sup_le
  intro j hj
  rcases mem_union.mp hj with hj | hj
  · exact (finiteAnnularMaximum_dominates J F x hj).trans (le_add_right le_rfl)
  · exact (finiteAnnularMaximum_dominates K F x hj).trans (le_add_left le_rfl)

theorem annularLocalMaxPairing_nonneg (I : SparseIntegerInterval) (F G : Finset ℤ) :
    0 ≤ annularLocalMaxPairing I F G := by
  exact sum_nonneg (fun _ _ => NNReal.coe_nonneg _)

end PrimeSquares
