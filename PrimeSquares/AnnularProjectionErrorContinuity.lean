import PrimeSquares.AnnularProjectionError
import PrimeSquares.AnnularFrequencyContinuity
namespace PrimeSquares
theorem annularProjectionError_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    Continuous (annularProjectionError N β) := by
  exact (annularOscillatoryModel_continuous hN β).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (sourceArcCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id))))
end PrimeSquares
