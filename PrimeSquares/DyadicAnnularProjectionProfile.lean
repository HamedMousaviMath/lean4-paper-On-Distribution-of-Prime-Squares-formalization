import PrimeSquares.AnnularProjectionErrorProfile
import PrimeSquares.DyadicAnnularFrequencyDecay
import PrimeSquares.DyadicAnnularScales
namespace PrimeSquares
theorem dyadicAnnularProjectionError_profile {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (θ : ℝ) (j : ℕ) :
    ‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖ ≤
      annularProjectionErrorConstant*((4 : ℝ)^j*((M : ℝ)^2*|θ|)) ∧
    ((4 : ℝ)^j*((M : ℝ)^2*|θ|))*‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖ ≤
      annularProjectionErrorConstant := by
  have h := (annularProjectionError_profile (dyadic_annular_scale_lower hM j) (hβ0 j) (hβ1 j) θ).2
  simpa only [dyadic_square_scale,mul_assoc] using h
end PrimeSquares
