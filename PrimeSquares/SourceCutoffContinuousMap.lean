import PrimeSquares.SourceArcCutoff
namespace PrimeSquares
noncomputable def sourceCutoffContinuousMap (s : ℕ) : C(ℝ,ℂ) :=
  ⟨fun x => Complex.ofReal (sourceArcCutoffScale s x),
    Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp
      (continuous_const.mul continuous_id))⟩
theorem sourceCutoffContinuousMap_support (s : ℕ) (x : ℝ) (hx : 1 ≤ |x|) :
    sourceCutoffContinuousMap s x = 0 := by
  have hp : (1 : ℝ) ≤ (16 : ℝ)^s := one_le_pow₀ (by norm_num)
  have hz : sourceArcCutoffScale s x = 0 := by
    by_contra h
    have hr := sourceArcCutoffScale_radius s h
    have hb : 1/(16 : ℝ)^s ≤ 1 := (div_le_one (by positivity)).mpr hp
    linarith
  simp only [sourceCutoffContinuousMap,ContinuousMap.coe_mk,hz,Complex.ofReal_zero]
end PrimeSquares
