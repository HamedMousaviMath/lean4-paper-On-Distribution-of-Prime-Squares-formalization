import PrimeSquares.WeightedAnnularBlockBounds
import PrimeSquares.AnnularModelDecay

namespace PrimeSquares

noncomputable def smallSourceDifferenceConstant : ℝ := 12*(16 : ℝ)^4/Real.pi

theorem smallSourceDifferenceConstant_pos : 0<smallSourceDifferenceConstant := by
  unfold smallSourceDifferenceConstant
  positivity

theorem localizedAnnularSource_small_difference {N s : ℕ} (hN : 2 ≤ N) (hs : s ≤ 4)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (x : ℝ) :
    ‖(localizedAnnularSource N (by omega) β s-localizedAnnularSource N (by omega) β 4) x‖ ≤
      (4*(16 : ℝ)^4)/(Real.pi*(N : ℝ)^2) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  by_cases hx : |x| ≤ 1/(2*(16 : ℝ)^4)
  · have hp : (16 : ℝ)^s ≤ (16 : ℝ)^4 := pow_le_pow_right₀ (by norm_num) hs
    have hsx : sourceArcCutoffScale s x=1 := sourceArcCutoffScale_core s
      (hx.trans (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hp (by norm_num))))
    have h4x := sourceArcCutoffScale_core 4 hx
    change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale s x)-
      annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale 4 x)‖ ≤ _
    rw [hsx,h4x,sub_self,norm_zero]
    positivity
  · have hout : ((N : ℝ)^2)/((2*(16 : ℝ)^4)*(N : ℝ)^2) ≤ |x| := by
      have he : ((N : ℝ)^2)/((2*(16 : ℝ)^4)*(N : ℝ)^2)=1/(2*(16 : ℝ)^4) := by field_simp
      rw [he]
      exact (lt_of_not_ge hx).le
    have hν := annularOscillatoryModel_outside_arc hN hβ0 hβ1
      (by positivity : (0 : ℝ)<2*(16 : ℝ)^4) (sq_pos_of_pos hNr) hout
    have hb : |sourceArcCutoffScale s x-sourceArcCutoffScale 4 x| ≤ 1 := by
      change |sourceArcCutoff ((16 : ℝ)^s*x)-sourceArcCutoff ((16 : ℝ)^4*x)| ≤ 1
      apply abs_le.mpr
      constructor <;> linarith [sourceArcCutoff_nonneg ((16 : ℝ)^s*x),sourceArcCutoff_nonneg ((16 : ℝ)^4*x),
        sourceArcCutoff_le_one ((16 : ℝ)^s*x),sourceArcCutoff_le_one ((16 : ℝ)^4*x)]
    change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale s x)-
      annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale 4 x)‖ ≤ _
    rw [←mul_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_one _)).trans
      (hν.trans_eq (by ring))

theorem circleAnnularSource_small_difference {N s : ℕ} (hN : 2 ≤ N) (hs : s ≤ 4)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℚ) :
    ‖circleAnnularSource N (by omega) β s r-circleAnnularSource N (by omega) β 4 r‖ ≤
      smallSourceDifferenceConstant/(N : ℝ)^2 := by
  let f := localizedAnnularSource N (by omega) β s-localizedAnnularSource N (by omega) β 4
  have hf : ∀ x,1 ≤ |x| → f x=0 := by
    intro x hx
    simp only [f,ContinuousMap.sub_apply,localizedAnnularSource_support N (by omega) β s x hx,
      localizedAnnularSource_support N (by omega) β 4 x hx,sub_self]
  apply (ContinuousMap.norm_le _ (by unfold smallSourceDifferenceConstant;positivity)).mpr
  intro θ
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) (θ-((r : ℝ) : PrimeCircle)) : ℝ)
  have hb := compactCircleLift_norm_bound f hf (localizedAnnularSource_small_difference hN hs hβ0 hβ1)
    (θ-((r : ℝ) : PrimeCircle))
  change ‖compactPeriodWindow f ξ‖ ≤ _ at hb
  change ‖compactPeriodWindow (localizedAnnularSource N (by omega) β s) ξ-
    compactPeriodWindow (localizedAnnularSource N (by omega) β 4) ξ‖ ≤ _
  have he : compactPeriodWindow f ξ=compactPeriodWindow (localizedAnnularSource N (by omega) β s) ξ-
      compactPeriodWindow (localizedAnnularSource N (by omega) β 4) ξ := by
    simp only [f,compactPeriodWindow,ContinuousMap.sub_apply]
    ring
  rw [he] at hb
  exact hb.trans_eq (by unfold smallSourceDifferenceConstant;ring)

end PrimeSquares
