import PrimeSquares.FiniteDecayConvolution
import PrimeSquares.KernelL1Operator

open scoped lp
namespace PrimeSquares

theorem decay_kernel_L1_norm (K : ℤ → ℂ) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (k : ℕ)
    (hK : ∀ z : ℤ, ‖K z‖ ≤ A*decayProfile H k z) (f : ℓ¹(ℤ, ℂ)) :
    ‖kernelL1Value K (decay_kernel_uniform K hA hH k hK) f‖ ≤ A*‖f‖ :=
  kernelL1Value_norm K (decay_kernel_uniform K hA hH k hK) f

theorem decay_kernel_finite_norm (K : ℤ → ℂ) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (k : ℕ)
    (hK : ∀ z : ℤ, ‖K z‖ ≤ A*decayProfile H k z) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution K F f x‖ ≤ A*∑ y ∈ F, ‖f y‖ := by
  calc
    _ ≤ A*∑ y ∈ F, decayProfile H k ((x-y : ℤ) : ℝ)*‖f y‖ :=
      finiteConvolution_profile_bound K hH k hK F f x
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro y _
      exact (mul_le_mul_of_nonneg_right (decayProfile_le_one hH k _) (norm_nonneg _)).trans_eq (one_mul _)

end PrimeSquares
