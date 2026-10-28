import PrimeSquares.SparseIntegerIntervals
import PrimeSquares.PositivePairing

/-!
# Why the abstract stopping lemma must specify dyadic scales

A positive convolution family can vanish at every dyadic index while
equaling the identity at N=3. Thus a local hypothesis tested only at
dyadic stopping values cannot control an unrestricted maximum for an
arbitrary family. Actual prime-square all-cutoff domination is proved
separately in PrimeFullMaximalComparison.
-/

open Finset
namespace PrimeSquares

def sparseNonDyadicKernel (N : ℕ) (z : ℤ) : ℂ := if N=3 ∧ z=0 then 1 else 0

theorem two_pow_ne_three (k : ℕ) : (2 : ℕ)^k ≠ 3 := by
  by_cases hk : k < 2
  · interval_cases k <;> norm_num
  · have hp : (4 : ℕ) ≤ 2^k := by
      simpa only [show (2 : ℕ)^2=4 by norm_num] using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
        (show 2 ≤ k by omega)
    omega

theorem sparseNonDyadicKernel_positive (N : ℕ) : NonnegativeKernel (sparseNonDyadicKernel N) := by
  intro z
  unfold sparseNonDyadicKernel
  split_ifs <;> norm_num

theorem sparseNonDyadicKernel_support (N : ℕ) {z : ℤ}
    (hz : z ∉ Icc (-(N : ℤ)) (N : ℤ)) : sparseNonDyadicKernel N z = 0 := by
  have hz0 : z ≠ 0 := by
    intro he
    subst z
    apply hz
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  simp only [sparseNonDyadicKernel, hz0, and_false, ite_false]

theorem sparseNonDyadicKernel_dyadic_zero (k : ℕ) (z : ℤ) : sparseNonDyadicKernel (2^k) z = 0 := by
  simp only [sparseNonDyadicKernel, two_pow_ne_three k, false_and, ite_false]

theorem sparseNonDyadic_local_pairing_zero (F G : Finset ℤ) (τ : ℤ → ℕ) :
    ‖∑ x ∈ G, indicatorConvolution (sparseNonDyadicKernel ((2 : ℕ)^(τ x))) F x‖ = 0 := by
  simp only [indicatorConvolution, sparseNonDyadicKernel_dyadic_zero, sum_const_zero, norm_zero]

theorem sparseNonDyadic_full_pairing_one :
    ‖restrictedKernelPairing (sparseNonDyadicKernel 3) {0} {0}‖ = 1 := by
  rw [restrictedKernelPairing, sum_singleton, indicatorConvolution, sum_singleton]
  norm_num [sparseNonDyadicKernel]

theorem sparseNonDyadic_maximum_positive :
    1 ≤ ⨆ N : ℕ, ‖indicatorConvolution (sparseNonDyadicKernel (N+1)) {0} 0‖ := by
  have hb : BddAbove (Set.range (fun N : ℕ => ‖indicatorConvolution (sparseNonDyadicKernel (N+1)) {0} 0‖)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨N, rfl⟩
    change ‖indicatorConvolution (sparseNonDyadicKernel (N+1)) {0} 0‖ ≤ 1
    by_cases hN : N+1=3 <;> simp [indicatorConvolution, sparseNonDyadicKernel, hN]
  have hd : ‖indicatorConvolution (sparseNonDyadicKernel (2+1)) {0} 0‖ ≤
      ⨆ N : ℕ, ‖indicatorConvolution (sparseNonDyadicKernel (N+1)) {0} 0‖ := le_ciSup hb 2
  simpa only [show (2 : ℕ)+1=3 by norm_num, indicatorConvolution, sum_singleton, sub_self,
    sparseNonDyadicKernel, and_self, ite_true, norm_one] using hd

end PrimeSquares
