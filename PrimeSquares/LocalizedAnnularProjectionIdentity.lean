import PrimeSquares.LocalizedAnnularProjectionError
import PrimeSquares.LocalizedAnnularSource
import PrimeSquares.LocalizedAnnularSmoothProjection
namespace PrimeSquares
theorem localizedAnnularProjectionError_identity (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) :
    localizedAnnularProjectionError N hN β s=localizedAnnularSource N hN β s-
      annularOscillatoryModel N β 0 • localizedAnnularSmoothProjection N s := by
  ext x
  change (annularOscillatoryModel N β x-annularOscillatoryModel N β 0*
      Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*x)))*sourceCutoffContinuousMap s x=
    annularOscillatoryModel N β x*sourceCutoffContinuousMap s x-
      annularOscillatoryModel N β 0*(Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*x))*sourceCutoffContinuousMap s x)
  ring
end PrimeSquares
