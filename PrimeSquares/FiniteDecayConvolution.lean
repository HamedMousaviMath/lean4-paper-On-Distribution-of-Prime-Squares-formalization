import PrimeSquares.DecayProfile
import PrimeSquares.FiniteSquareOperators

open Finset
namespace PrimeSquares

theorem finiteConvolution_profile_bound (K : ℤ → ℂ) {A H : ℝ} (_hH : 0 < H) (k : ℕ)
    (hK : ∀ z : ℤ, ‖K z‖ ≤ A*decayProfile H k z)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution K F f x‖ ≤ A*∑ y ∈ F, decayProfile H k ((x-y : ℤ) : ℝ)*‖f y‖ := by
  calc
    _ ≤ ∑ y ∈ F, ‖K (x-y)*f y‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ F, A*(decayProfile H k ((x-y : ℤ) : ℝ)*‖f y‖) := by
      apply sum_le_sum
      intro y _
      rw [norm_mul,←mul_assoc]
      exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
    _ = _ := (mul_sum ..).symm

theorem decay_kernel_uniform (K : ℤ → ℂ) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (k : ℕ)
    (hK : ∀ z : ℤ, ‖K z‖ ≤ A*decayProfile H k z) : ∀ z : ℤ, ‖K z‖ ≤ A := by
  intro z
  exact (hK z).trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (decayProfile_le_one hH k z) hA)

end PrimeSquares
