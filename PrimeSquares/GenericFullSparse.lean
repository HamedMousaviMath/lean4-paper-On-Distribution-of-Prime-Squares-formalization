import PrimeSquares.GenericFullMaximum
import PrimeSquares.PrimeSparseRoot

set_option autoImplicit false
open Finset
open scoped NNReal
namespace PrimeSquares

def genericFiniteTestRoot (F G : Finset ℤ) (J : Finset ℕ) : SparseIntegerInterval :=
  integerCenteredBall 0 (primeSparseRadius F G+∑ j ∈ J,(2:ℕ)^j)

theorem genericFiniteTestRoot_contains (F G : Finset ℤ) (J : Finset ℕ) :
    F ⊆ (genericFiniteTestRoot F G J).points ∧ G ⊆ (genericFiniteTestRoot F G J).points := by
  have hall : F ∪ G ⊆ (genericFiniteTestRoot F G J).points := by
    intro z hz
    change z ∈ (integerCenteredBall 0 (primeSparseRadius F G+∑ j ∈ J,(2:ℕ)^j)).points
    rw [integerCenteredBall_mem]
    simp only [zero_sub,abs_neg]
    have ha := primeSparseRadius_abs hz
    have hbig : (primeSparseRadius F G:ℤ) ≤ (primeSparseRadius F G+∑ j ∈ J,(2:ℕ)^j:ℕ) := by
      exact_mod_cast (Nat.le_add_right (primeSparseRadius F G) (∑ j ∈ J,(2:ℕ)^j))
    exact ha.trans hbig
  exact ⟨Finset.union_subset_iff.mp hall |>.1,Finset.union_subset_iff.mp hall |>.2⟩

theorem genericFiniteTestRoot_scales (F G : Finset ℤ) (J : Finset ℕ) :
    ∀ j ∈ J,(2:ℕ)^j ≤ (genericFiniteTestRoot F G J).length := by
  intro j hj
  have h := Finset.single_le_sum (s:=J) (f:=fun i => (2:ℕ)^i) (fun _ _ => Nat.zero_le _) hj
  change _ ≤ 2*(primeSparseRadius F G+∑ i ∈ J,(2:ℕ)^i)+1
  omega

theorem genericFiniteTest_le_root {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (F G : Finset ℤ) (J : Finset ℕ) :
    (∑ x ∈ G,(genericDyadicMaximum T J F x:ℝ)) ≤
      genericLocalMaxPairing T m (genericFiniteTestRoot F G J) F G := by
  have hc := genericFiniteTestRoot_contains F G J
  have hF : F ∩ ((genericFiniteTestRoot F G J).oddDilate m).points=F :=
    Finset.inter_eq_left.mpr (hc.1.trans (integerInterval_subset_oddDilate _ m))
  unfold genericLocalMaxPairing
  rw [Finset.inter_eq_left.mpr hc.2,hF]
  apply Finset.sum_le_sum
  intro x _
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro j hj
  exact Finset.le_sup (f:=fun i => ‖positiveDyadicValue T i F x‖₊)
    ((mem_linearDyadicIndices _ j).mpr (genericFiniteTestRoot_scales F G J j hj))

noncomputable def genericFullDyadicPairing {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (F G : Finset ℤ) : ℝ := ∑ x ∈ G,genericFullDyadicMaximum T F x

theorem genericPositiveFullSparse {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) (F G : Finset ℤ) :
    ∃ S : Finset SparseIntegerInterval,IntegerSparseFamily (1/4) S ∧
      |genericFullDyadicPairing T F G| ≤ (2*K)*∑ I ∈ S,genericDensitySparseCost m Ψ I F G := by
  obtain ⟨J,hJ⟩ := genericFullDyadicMaximum_finite_test T m hC Ψ hlocal F G
  obtain ⟨S,_,hS,hval⟩ := genericFiniteSparse_from_local_profile T m hC Ψ hlocal
    (genericFiniteTestRoot F G J) F G
  have hnonneg : 0 ≤ genericFullDyadicPairing T F G :=
    Finset.sum_nonneg (fun x _ => genericFullDyadicMaximum_nonneg T m hC Ψ hlocal F x)
  refine ⟨S,integerSparseFamily_mono hS (by norm_num),?_⟩
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ 2*∑ x ∈ G,(genericDyadicMaximum T J F x:ℝ) := hJ
    _ ≤ 2*genericLocalMaxPairing T m (genericFiniteTestRoot F G J) F G :=
      mul_le_mul_of_nonneg_left (genericFiniteTest_le_root T m F G J) (by norm_num)
    _ ≤ 2*(K*∑ I ∈ S,genericDensitySparseCost m Ψ I F G) :=
      mul_le_mul_of_nonneg_left hval (by norm_num)
    _ = _ := by ring

theorem source_dyadic_sparse_recursion {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ) (hK : 0 < K)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ F G : Finset ℤ,∃ S : Finset SparseIntegerInterval,
      IntegerSparseFamily (1/4) S ∧
      |genericFullDyadicPairing T F G| ≤ Kout*∑ I ∈ S,genericDensitySparseCost m Ψ I F G := by
  exact ⟨2*K,by positivity,genericPositiveFullSparse T m hC Ψ hlocal⟩

end PrimeSquares
