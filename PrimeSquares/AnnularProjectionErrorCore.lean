import PrimeSquares.AnnularProjectionError
namespace PrimeSquares
theorem annularProjectionError_core (N : ℕ) (β : ℝ) {θ : ℝ}
    (hθ : (N : ℝ)^2*|θ| ≤ 1/2) :
    annularProjectionError N β θ=annularOscillatoryModel N β θ-annularOscillatoryModel N β 0 := by
  have hb : sourceArcCutoff ((N : ℝ)^2*θ)=1 := sourceArcCutoff_core (by
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg (N : ℝ))] using hθ)
  simp only [annularProjectionError,hb,Complex.ofReal_one,mul_one]
end PrimeSquares
