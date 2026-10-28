import PrimeSquares.GoldbachWeightedIntegralConstant

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_W_integrable_general (α : ℝ) (hα : 1<α) :
    IntervalIntegrable (fun t : ℝ=>(t-2+(t-1)*Real.log (t-1))/
      (t^2*(t-1)*Real.sqrt (1-t/(2*α)))) volume 2 (2*α) := by
  let b := 2*α
  let f := fun t : ℝ=>(t-2+(t-1)*Real.log (t-1))/(t^2*(t-1))
  have hb : (2:ℝ)<b := by dsimp only [b];linarith
  have hb0 : 0<b := by linarith
  have hf : ContinuousOn f (Set.uIcc 2 b) := by
    rw [Set.uIcc_of_le hb.le]
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht1 : t-1≠0 := by linarith [ht.1]
    have hden : t^2*(t-1)≠0 := mul_ne_zero (pow_ne_zero 2 ht0) ht1
    apply ContinuousAt.continuousWithinAt
    dsimp only [f]
    fun_prop
  have hp := intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=b-2)
    (by norm_num : (-1:ℝ)< -(1/2:ℝ))
  have hcomp := (hp.comp_sub_left b).symm
  simp only [sub_zero,sub_sub_cancel] at hcomp
  have hi := (hcomp.const_mul (Real.sqrt b)).mul_continuousOn hf
  have his := (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mp hi
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mpr
  apply his.congr_fun _ measurableSet_Icc
  intro t ht
  have htB : 0≤b-t := by linarith [ht.2]
  have hid : 1-t/b=(b-t)/b := by field_simp
  have hs : Real.sqrt (1-t/b)=Real.sqrt (b-t)/Real.sqrt b := by
    rw [hid,Real.sqrt_div htB]
  dsimp only [f]
  change Real.sqrt b*((b-t)^(-(1/2:ℝ)))*
    ((t-2+(t-1)*Real.log (t-1))/(t^2*(t-1)))=_
  rw [Real.rpow_neg htB,←Real.sqrt_eq_rpow]
  change Real.sqrt b*(Real.sqrt (b-t))⁻¹*
    ((t-2+(t-1)*Real.log (t-1))/(t^2*(t-1)))=
      (t-2+(t-1)*Real.log (t-1))/(t^2*(t-1)*Real.sqrt (1-t/b))
  rw [hs]
  by_cases hend : b=t
  · rw [hend]
    norm_num
  · have htlt : t<b := lt_of_le_of_ne ht.2 (Ne.symm hend)
    have hroot : Real.sqrt (b-t)≠0 := (Real.sqrt_pos.mpr (sub_pos.mpr htlt)).ne'
    have hbroot : Real.sqrt b≠0 := (Real.sqrt_pos.mpr hb0).ne'
    field_simp

theorem goldbach_weighted_W_nonneg_general (α : ℝ) (hα : 1<α) : 0≤goldbachWeightedW α := by
  unfold goldbachWeightedW
  apply mul_nonneg (by positivity)
  rw [intervalIntegral.integral_of_le (show (2:ℝ)≤2*α by linarith)]
  apply setIntegral_nonneg measurableSet_Ioc
  intro t ht
  have ht2 : 2≤t := by linarith [ht.1]
  have hlog : 0≤Real.log (t-1) := Real.log_nonneg (by linarith)
  apply div_nonneg
  · exact add_nonneg (by linarith) (mul_nonneg (by linarith) hlog)
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (Real.sqrt_nonneg _)

end PrimeSquares
