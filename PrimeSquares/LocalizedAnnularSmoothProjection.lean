import PrimeSquares.SourceCutoffContinuousMap
import PrimeSquares.CompactCirclePeriodization
namespace PrimeSquares
noncomputable def localizedAnnularSmoothProjection (N s : ℕ) : C(ℝ,ℂ) :=
  ⟨fun x => Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*x))*sourceCutoffContinuousMap s x,
    by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp
          (continuous_const.mul continuous_id))
      · exact (sourceCutoffContinuousMap s).continuous⟩
theorem localizedAnnularSmoothProjection_support (N s : ℕ) (x : ℝ) (hx : 1 ≤ |x|) :
    localizedAnnularSmoothProjection N s x=0 := by
  simp only [localizedAnnularSmoothProjection,ContinuousMap.coe_mk,
    sourceCutoffContinuousMap_support s x hx,mul_zero]
end PrimeSquares
