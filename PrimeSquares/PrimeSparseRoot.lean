import PrimeSquares.FiniteAnnularMaximum

/-!
# An explicit finite root for every pair of finite sets

The root is large enough that every annular scale outside its spatial
cutoff vanishes on the actual test set. Thus no unproved passage to a
limit of sparse families is needed for finite indicators.
-/

open Finset
open scoped NNReal
namespace PrimeSquares

def primeSparseRadius (F G : Finset ℤ) : ℕ := 1+∑ z ∈ F ∪ G, z.natAbs

def primeSparseRoot (F G : Finset ℤ) : SparseIntegerInterval where
  left := -(primeSparseRadius F G : ℤ)
  length := 8*primeSparseRadius F G
  length_pos := by unfold primeSparseRadius; omega

theorem primeSparseRadius_abs {F G : Finset ℤ} {z : ℤ} (hz : z ∈ F ∪ G) :
    |z| ≤ (primeSparseRadius F G : ℤ) := by
  have hs := Finset.single_le_sum (s := F ∪ G) (f := Int.natAbs) (fun _ _ => Nat.zero_le _) hz
  have hn : z.natAbs ≤ primeSparseRadius F G := by dsimp [primeSparseRadius]; omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hn

theorem primeSparseRoot_contains (F G : Finset ℤ) :
    F ⊆ (primeSparseRoot F G).points ∧ G ⊆ (primeSparseRoot F G).points := by
  have hp : 0 < primeSparseRadius F G := by unfold primeSparseRadius; omega
  have hall : F ∪ G ⊆ (primeSparseRoot F G).points := by
    intro z hz
    have ha := primeSparseRadius_abs hz
    rw [abs_le] at ha
    rw [integerInterval_mem_points]
    simp only [primeSparseRoot, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  exact ⟨union_subset_iff.mp hall |>.1, union_subset_iff.mp hall |>.2⟩

theorem annularDyadicValue_zero_of_far (j : ℕ) (F : Finset ℤ) (x : ℤ) (D : ℕ)
    (hfar : ∀ y ∈ F, x-y ≤ (D : ℤ)) (hscale : 4*D < ((2 : ℕ)^j*2)^2) :
    annularDyadicValue j F x = 0 := by
  unfold annularDyadicValue indicatorConvolution
  apply sum_eq_zero
  intro y hy
  apply finiteSquareKernel_eq_zero
  intro hz
  obtain ⟨n, hn, he⟩ := mem_image.mp hz
  have hhalf : (((2 : ℕ)^j*2)/2) = (2 : ℕ)^j := by omega
  have hnj : (2 : ℕ)^j < n := by simpa only [hhalf] using (mem_Ioc.mp hn).1
  have hnjI : (((2 : ℕ)^j : ℕ) : ℤ) < n := by exact_mod_cast hnj
  have hscaleI : (4 : ℤ)*D < ((((2 : ℕ)^j*2 : ℕ) : ℤ))^2 := by exact_mod_cast hscale
  push_cast at hscaleI
  have hs : ((((2 : ℕ)^j : ℕ) : ℤ))^2 < (n : ℤ)^2 :=
    (sq_lt_sq₀ (Int.natCast_nonneg _) (Int.natCast_nonneg _)).mpr hnjI
  push_cast at hs
  have hxy := hfar y hy
  nlinarith

theorem primeSparseRoot_tail_zero (F G : Finset ℤ) {x : ℤ} (hx : x ∈ G) (j : ℕ)
    (hscale : ¬ ((2 : ℕ)^j*2)^2 ≤ (primeSparseRoot F G).length) :
    annularDyadicValue j F x = 0 := by
  apply annularDyadicValue_zero_of_far j F x (2*primeSparseRadius F G)
  · intro y hy
    have hxA := primeSparseRadius_abs (mem_union_right F hx)
    have hyA := primeSparseRadius_abs (mem_union_left G hy)
    rw [abs_le] at hxA hyA
    push_cast
    omega
  · change ¬ ((2 : ℕ)^j*2)^2 ≤ 8*primeSparseRadius F G at hscale
    omega

theorem primeSparseRoot_dominates (F G : Finset ℤ) {x : ℤ} (hx : x ∈ G) (j : ℕ) :
    ‖annularDyadicValue j F x‖ ≤
      (truncatedAnnularMaximum (primeSparseRoot F G).length F x : ℝ) := by
  by_cases hs : ((2 : ℕ)^j*2)^2 ≤ (primeSparseRoot F G).length
  · exact NNReal.coe_le_coe.mpr (finiteAnnularMaximum_dominates _ F x
      ((mem_dyadicSpatialIndices _ j).mpr hs))
  · rw [primeSparseRoot_tail_zero F G hx j hs, norm_zero]
    exact NNReal.coe_nonneg _

theorem primeSparseRoot_pairing (F G : Finset ℤ) :
    annularLocalMaxPairing (primeSparseRoot F G) F G =
      ∑ x ∈ G, (truncatedAnnularMaximum (primeSparseRoot F G).length F x : ℝ) := by
  have hc := primeSparseRoot_contains F G
  have hF : F ∩ (primeSparseRoot F G).five.points = F :=
    inter_eq_left.mpr (hc.1.trans (integerInterval_points_subset_five _))
  simp only [annularLocalMaxPairing, inter_eq_left.mpr hc.2, hF]

end PrimeSquares
