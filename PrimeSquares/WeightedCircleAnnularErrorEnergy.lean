import PrimeSquares.CircleAnnularErrorEnergy
open Finset
namespace PrimeSquares
theorem circleAnnularProjectionError_weighted_energy {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 1 ≤ s)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (r : ℚ) (c : ℕ → ℂ) {A : ℝ} (hc : ∀ j,‖c j‖ ≤ A) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖c j*circleAnnularProjectionError ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r θ‖^2) ≤
      A^2*((34/15 : ℝ)*annularProjectionErrorConstant^2) := by
  calc
    _ ≤ ∑ j ∈ J,A^2*‖circleAnnularProjectionError ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r θ‖^2 := by
        apply sum_le_sum
        intro j _
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _)
    _ = A^2*(∑ j ∈ J,‖circleAnnularProjectionError ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r θ‖^2) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (circleAnnularProjectionError_finite_energy hM hs β hβ0 hβ1 r J θ) (sq_nonneg _)
end PrimeSquares
