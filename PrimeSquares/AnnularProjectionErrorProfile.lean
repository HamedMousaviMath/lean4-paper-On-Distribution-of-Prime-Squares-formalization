import PrimeSquares.AnnularProjectionErrorNear
import PrimeSquares.AnnularProjectionErrorFar
namespace PrimeSquares
noncomputable def annularProjectionErrorConstant : ℝ := Real.pi+3+2/Real.pi
theorem annularProjectionError_profile {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    0 < annularProjectionErrorConstant ∧
    ‖annularProjectionError N β θ‖ ≤ annularProjectionErrorConstant*((N : ℝ)^2*|θ|) ∧
    ((N : ℝ)^2*|θ|)*‖annularProjectionError N β θ‖ ≤ annularProjectionErrorConstant := by
  have hp : 0 < 2/Real.pi := by positivity
  have ha : 0 ≤ (N : ℝ)^2*|θ| := by positivity
  refine ⟨by unfold annularProjectionErrorConstant;positivity,?_,?_⟩
  · exact (annularProjectionError_near hN hβ1 θ).trans
      (mul_le_mul_of_nonneg_right (by unfold annularProjectionErrorConstant;linarith) ha)
  · exact (annularProjectionError_far hN hβ0 hβ1 θ).trans
      (by unfold annularProjectionErrorConstant;linarith [Real.pi_pos])
end PrimeSquares
