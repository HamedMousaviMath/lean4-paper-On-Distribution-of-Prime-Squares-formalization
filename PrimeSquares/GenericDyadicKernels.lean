import PrimeSquares.LinearGoodPointMass
import PrimeSquares.AnnularStoppingSupport
import PrimeSquares.AdmissibleAnnularLinearization

set_option autoImplicit false
open Finset
namespace PrimeSquares

def SparseIntegerInterval.oddDilate (I : SparseIntegerInterval) (m : ℕ) : SparseIntegerInterval where
  left := I.left-(m:ℤ)*I.length
  length := (2*m+1)*I.length
  length_pos := Nat.mul_pos (by omega) I.length_pos

theorem integerInterval_subset_oddDilate (I : SparseIntegerInterval) (m : ℕ) :
    I.points ⊆ (I.oddDilate m).points := by
  intro x hx
  rw [integerInterval_mem_points] at hx ⊢
  simp only [SparseIntegerInterval.oddDilate,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hprod : 0 ≤ (m:ℤ)*I.length := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  constructor <;> nlinarith

theorem integerInterval_oddDilate_subset {I R : SparseIntegerInterval} (m : ℕ)
    (hIR : I.points ⊆ R.points) : (I.oddDilate m).points ⊆ (R.oddDilate m).points := by
  have hb := (integerInterval_subset_iff I R).mp hIR
  have hn := integerInterval_subset_length hIR
  have hnR : (I.length:ℤ)≤R.length := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hnR (Int.natCast_nonneg m)
  rw [integerInterval_subset_iff]
  simp only [SparseIntegerInterval.oddDilate,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  constructor <;> nlinarith

theorem integerBall_subset_oddDilate {C : ℝ} (I : SparseIntegerInterval) (m N : ℕ)
    (hC : C ≤ (m:ℝ)) (hN : N ≤ I.length) {x y : ℤ} (hx : x ∈ I.points)
    (hxy : |((x-y:ℤ):ℝ)| ≤ C*(N:ℝ)) : y ∈ (I.oddDilate m).points := by
  have hNR : (N:ℝ)≤I.length := by exact_mod_cast hN
  have hbound : C*(N:ℝ) ≤ (m:ℝ)*I.length :=
    mul_le_mul hC hNR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd : |x-y| ≤ (m:ℤ)*I.length := by exact_mod_cast hxy.trans hbound
  rw [abs_le] at hd
  rw [integerInterval_mem_points] at hx ⊢
  simp only [SparseIntegerInterval.oddDilate,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  constructor <;> nlinarith

/-- An arbitrary positive convolution family at physical scales 2^j.
There is no analytic estimate or sparse conclusion in this record. -/
structure PositiveDyadicConvolutionFamily (C : ℝ) where
  kernel : ℕ → ℤ → ℂ
  nonnegative : ∀ j,NonnegativeKernel (kernel j)
  support : ∀ (j : ℕ) (z : ℤ),C*(2:ℝ)^j < |(z:ℝ)| → kernel j z=0

noncomputable def positiveDyadicValue {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (j : ℕ) (F : Finset ℤ) (x : ℤ) : ℂ := indicatorConvolution (T.kernel j) F x

theorem positiveDyadicValue_positive {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    (positiveDyadicValue T j F x).im=0 ∧ 0 ≤ (positiveDyadicValue T j F x).re :=
  ⟨indicatorConvolution_im_zero (T.nonnegative j) F x,
    indicatorConvolution_re_nonneg (T.nonnegative j) F x⟩

theorem positiveDyadicValue_localize {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (I : SparseIntegerInterval) (m j : ℕ) (hC : C ≤ (m:ℝ))
    (hN : (2:ℕ)^j ≤ I.length) (F : Finset ℤ) {x : ℤ} (hx : x ∈ I.points) :
    positiveDyadicValue T j F x=positiveDyadicValue T j (F ∩ (I.oddDilate m).points) x := by
  unfold positiveDyadicValue indicatorConvolution
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro y hyF hy
  apply T.support
  by_contra! hdist
  have hyI := integerBall_subset_oddDilate I m (2^j) hC hN hx
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.cast_sub] using hdist)
  exact hy (Finset.mem_inter.mpr ⟨hyF,hyI⟩)

theorem positiveDyadicValue_restrict_twice {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    {I R : SparseIntegerInterval} (hIR : I.points ⊆ R.points) (m j : ℕ)
    (hC : C ≤ (m:ℝ)) (hN : (2:ℕ)^j ≤ I.length) (F : Finset ℤ) {x : ℤ}
    (hx : x ∈ I.points) :
    positiveDyadicValue T j (F ∩ (R.oddDilate m).points) x=
      positiveDyadicValue T j (F ∩ (I.oddDilate m).points) x := by
  rw [positiveDyadicValue_localize T I m j hC hN (F ∩ (R.oddDilate m).points) hx]
  congr 1
  have hd := integerInterval_oddDilate_subset m hIR
  ext y
  simp only [Finset.mem_inter]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hd h.2⟩,h.2⟩⟩

end PrimeSquares
