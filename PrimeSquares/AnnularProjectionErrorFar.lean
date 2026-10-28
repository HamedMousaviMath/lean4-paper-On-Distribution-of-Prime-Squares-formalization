import PrimeSquares.AnnularProjectionErrorSize
import PrimeSquares.AnnularModelDecay
namespace PrimeSquares
theorem annularProjectionError_far {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ((N : ℝ)^2*|θ|)*‖annularProjectionError N β θ‖ ≤ 1+2/Real.pi := by
  by_cases h : 1 ≤ (N : ℝ)^2*|θ|
  · have hb : sourceArcCutoff ((N : ℝ)^2*θ)=0 := sourceArcCutoff_zero (by
      simpa only [abs_mul,abs_of_nonneg (sq_nonneg (N : ℝ))] using h)
    simp only [annularProjectionError,hb,Complex.ofReal_zero,mul_zero,sub_zero]
    exact (annularOscillatoryModel_frequency_mass hN hβ0 hβ1 θ).trans (by linarith)
  · have hb := annularProjectionError_norm_one hN hβ1 θ
    have he := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (N : ℝ)^2*|θ|)
    have hp : 0 < 2/Real.pi := by positivity
    nlinarith
end PrimeSquares
