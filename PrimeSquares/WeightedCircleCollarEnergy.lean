import PrimeSquares.CircleCollarCountableMaximum

open Finset
namespace PrimeSquares

theorem circleAnnularCollar_weighted_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q b : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (s : ℕ) (center : ℝ) (c : ℕ → ℂ) (hc : ∀ j,‖c j‖ ≤ b) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖(c j • circleAnnularCollar ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center) θ‖^2) ≤
      (b*(24*q/(Real.pi*Q)))^2 := by
  calc
    _ ≤ ∑ j ∈ J,b^2*‖circleAnnularCollar ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center θ‖^2 := by
      apply sum_le_sum
      intro j _
      simp only [ContinuousMap.smul_apply,smul_eq_mul,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _)
    _ = b^2*(∑ j ∈ J,‖circleAnnularCollar ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center θ‖^2) := (mul_sum _ _ _).symm
    _ ≤ b^2*(24*q/(Real.pi*Q))^2 := mul_le_mul_of_nonneg_left (circleAnnularCollar_finite_energy hM β hβ0 hβ1 hq hQ s center J θ) (sq_nonneg b)
    _ = _ := (mul_pow _ _ _).symm

end PrimeSquares
