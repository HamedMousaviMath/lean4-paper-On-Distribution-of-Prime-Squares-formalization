import PrimeSquares.AnnularProjectionErrorSize
import PrimeSquares.AnnularProjectionErrorCore
namespace PrimeSquares
theorem annularProjectionError_near {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularProjectionError N β θ‖ ≤ (Real.pi+2)*((N : ℝ)^2*|θ|) := by
  by_cases h : (N : ℝ)^2*|θ| ≤ 1/2
  · rw [annularProjectionError_core N β h]
    exact (annularOscillatoryModel_small_frequency hN hβ θ).trans (by
      have hp := Real.pi_pos
      have ha : 0 ≤ (N : ℝ)^2*|θ| := by positivity
      nlinarith)
  · have he := annularProjectionError_norm_one hN hβ θ
    have hp := Real.pi_pos
    have ha : 0 ≤ Real.pi*((N : ℝ)^2*|θ|) := by positivity
    linarith
end PrimeSquares
