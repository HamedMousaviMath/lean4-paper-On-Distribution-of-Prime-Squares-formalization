import PrimeSquares.LocalizedAnnularProjectionIdentity
import PrimeSquares.CircleAnnularProjectionError
import PrimeSquares.CircleAnnularSource
import PrimeSquares.CircleAnnularSmoothProjection
namespace PrimeSquares
theorem circleAnnularProjectionError_identity (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) (r : ℚ) :
    circleAnnularProjectionError N hN β s r=circleAnnularSource N hN β s r-
      annularOscillatoryModel N β 0 • circleAnnularSmoothProjection N s r := by
  ext θ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) (θ-((r : ℝ) : PrimeCircle)) : ℝ)
  change compactPeriodWindow (localizedAnnularProjectionError N hN β s) x=
    compactPeriodWindow (localizedAnnularSource N hN β s) x-
      annularOscillatoryModel N β 0*compactPeriodWindow (localizedAnnularSmoothProjection N s) x
  rw [localizedAnnularProjectionError_identity]
  simp only [compactPeriodWindow,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring
end PrimeSquares
