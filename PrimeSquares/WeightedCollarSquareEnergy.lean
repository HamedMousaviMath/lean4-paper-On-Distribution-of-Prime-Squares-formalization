import PrimeSquares.FiniteCollarSquareEnergy

open Finset
namespace PrimeSquares

theorem collarFactor_weighted_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q b : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (c : ℕ → ℂ) (hc : ∀ j,‖c j‖ ≤ b) (J : Finset ℕ) (θ : ℝ) :
    (∑ j ∈ J,‖c j*annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) ≤
      b^2*(8*q/(Real.pi*Q))^2 := by
  calc
    _ ≤ ∑ j ∈ J,b^2*‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2 := by
      apply sum_le_sum
      intro j _
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _)
    _ = b^2*(∑ j ∈ J,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) := (mul_sum J _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (collarFactor_finite_square_simple hM β hβ0 hβ1 hq hQ J θ) (sq_nonneg b)

end PrimeSquares
