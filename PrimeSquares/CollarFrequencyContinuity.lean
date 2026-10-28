import PrimeSquares.WeightedCollarSquareEnergy
import PrimeSquares.AnnularFrequencyContinuity

namespace PrimeSquares

theorem annularCollarMask_continuous (N q Q : ℝ) : Continuous (annularCollarMask N q Q) :=
  continuous_const.sub (sourceArcCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id))

theorem annularCollarFactor_continuous (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) :
    Continuous (annularCollarFactor N β q Q) :=
  (annularOscillatoryModel_continuous hN β).mul (Complex.continuous_ofReal.comp (annularCollarMask_continuous N q Q))

end PrimeSquares
