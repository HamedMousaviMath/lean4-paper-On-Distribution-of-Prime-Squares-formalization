import PrimeSquares.FourierKernels

open Finset MeasureTheory
namespace PrimeSquares

theorem fourierKernel_uniform_bound (m : C(PrimeCircle, ℂ)) {B : ℝ}
    (hm : ∀ θ, ‖m θ‖ ≤ B) (x : ℤ) : ‖fourierKernel m x‖ ≤ B := by
  rw [fourierKernel_coefficient, fourierCoeff]
  have h : ∀ᵐ θ : PrimeCircle ∂AddCircle.haarAddCircle,
      ‖fourier (-(-x)) θ • m θ‖ ≤ B := Filter.Eventually.of_forall fun θ => by
    rw [norm_smul, show ‖fourier (-(-x)) θ‖ = 1 from Circle.norm_coe _, one_mul]
    exact hm θ
  simpa using norm_integral_le_of_norm_le_const h

theorem fourierKernel_finite_input_bound (m : C(PrimeCircle, ℂ)) {B : ℝ}
    (hm : ∀ θ, ‖m θ‖ ≤ B) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution (fourierKernel m) F f x‖ ≤ B*∑ y ∈ F, ‖f y‖ := by
  calc
    _ ≤ ∑ y ∈ F, ‖fourierKernel m (x-y)*f y‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ F, B*‖f y‖ := by
      apply sum_le_sum
      intro y _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (fourierKernel_uniform_bound m hm _) (norm_nonneg _)
    _ = _ := (mul_sum ..).symm

end PrimeSquares
