import PrimeSquares.FourierL1Operator

open scoped lp
namespace PrimeSquares

theorem fourierL1Operator_kernel_bound (m : C(PrimeCircle, ℂ)) {B : ℝ}
    (hK : ∀ x, ‖fourierKernel m x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) :
    ‖fourierL1Operator m f‖ ≤ B*‖f‖ := by
  apply lp.norm_le_of_forall_le'
  intro x
  exact kernelL1Sum_bound _ hK f x

theorem fourierL1Operator_opNorm_kernel_bound (m : C(PrimeCircle, ℂ)) {B : ℝ}
    (hK : ∀ x, ‖fourierKernel m x‖ ≤ B) : ‖fourierL1Operator m‖ ≤ B :=
  (fourierL1Operator m).opNorm_le_bound ((norm_nonneg _).trans (hK 0))
    (fourierL1Operator_kernel_bound m hK)

end PrimeSquares
