import PrimeSquares.SourceArcCutoff
import PrimeSquares.CompactCirclePeriodization
namespace PrimeSquares
noncomputable def scaledSmoothCutoffMap (a : ℝ) : C(ℝ,ℂ) :=
  ⟨fun x => Complex.ofReal (sourceArcCutoff (a*x)),
    Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp
      (continuous_const.mul continuous_id))⟩
theorem scaledSmoothCutoff_radius {a x : ℝ} (ha : 0 < a)
    (hx : sourceArcCutoff (a*x) ≠ 0) : |x| < 1/a := by
  have h := sourceArcCutoff_radius hx
  rw [abs_mul,abs_of_pos ha] at h
  exact (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using h)
theorem scaledSmoothCutoffMap_support (a : ℝ) (ha : 1 ≤ a) (x : ℝ) (hx : 1 ≤ |x|) :
    scaledSmoothCutoffMap a x=0 := by
  have hz : sourceArcCutoff (a*x)=0 := sourceArcCutoff_zero (by
    rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ a)]
    nlinarith)
  simp only [scaledSmoothCutoffMap,ContinuousMap.coe_mk,hz,Complex.ofReal_zero]
end PrimeSquares
