import PrimeSquares.AnnularSmallFrequencyDifference
import PrimeSquares.SourceArcCutoff
namespace PrimeSquares
noncomputable def annularProjectionError (N : ℕ) (β θ : ℝ) : ℂ :=
  annularOscillatoryModel N β θ-annularOscillatoryModel N β 0*
    Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*θ))
theorem annularProjectionError_zero (N : ℕ) (β : ℝ) : annularProjectionError N β 0=0 := by
  have h : sourceArcCutoff 0=1 := sourceArcCutoff_core (by norm_num)
  simp only [annularProjectionError,mul_zero,h,Complex.ofReal_one,mul_one,sub_self]
end PrimeSquares
