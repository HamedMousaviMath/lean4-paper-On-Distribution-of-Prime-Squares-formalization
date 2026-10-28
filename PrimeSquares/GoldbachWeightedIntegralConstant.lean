import PrimeSquares.GoldbachWeightedMeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedInnerPrimitive (s v : ℝ) : ℝ :=
  (Real.log v-Real.log (s-v)+s/(s-v))/s^2

noncomputable def goldbachWeightedInnerIntegral (r : ℝ) : ℝ :=
  ∫ v in (4/9:ℝ)..((1-r)/2),1/(v*(1-r-v)^2)

noncomputable def goldbachWeightedW (α : ℝ) : ℝ :=
  α/(4*Real.sqrt 2)*∫ t in (2:ℝ)..(2*α),
    (t-2+(t-1)*Real.log (t-1))/(t^2*(t-1)*Real.sqrt (1-t/(2*α)))

theorem goldbach_weighted_inner_primitive_deriv (s v : ℝ) (hv : 0<v) (hsv : v<s) :
    HasDerivAt (goldbachWeightedInnerPrimitive s) (1/(v*(s-v)^2)) v := by
  have hs : 0<s := hv.trans hsv
  have hsv0 : s-v≠0 := (sub_pos.mpr hsv).ne'
  have hd := (hasDerivAt_const v s).sub (hasDerivAt_id v)
  have hlog := (Real.hasDerivAt_log hv.ne').sub ((Real.hasDerivAt_log hsv0).comp v hd)
  have hrat := (hasDerivAt_const v s).div hd hsv0
  convert (hlog.add hrat).div_const (s^2) using 1
  · rfl
  · dsimp only [Pi.sub_apply,Function.comp_apply,id_eq]
    field_simp
    ring

theorem goldbach_weighted_inner_integral (s a : ℝ) (ha : 0<a) (haS : a≤s/2) :
    (∫ v in a..s/2,1/(v*(s-v)^2))=
      ((s-2*a)/(s-a)+Real.log ((s-a)/a))/s^2 := by
  have hs : 0<s := by linarith
  have hsa : 0<s-a := by linarith
  have hcont : ContinuousOn (fun v : ℝ=>1/(v*(s-v)^2)) (Set.uIcc a (s/2)) := by
    rw [Set.uIcc_of_le haS]
    intro v hv
    have hv0 : v≠0 := by linarith [hv.1]
    have hsv0 : s-v≠0 := by linarith [hv.2]
    have hden : v*(s-v)^2≠0 := mul_ne_zero hv0 (pow_ne_zero 2 hsv0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv=>goldbach_weighted_inner_primitive_deriv s v
      (by rw [Set.uIcc_of_le haS] at hv;linarith [hv.1])
      (by rw [Set.uIcc_of_le haS] at hv;linarith [hv.2])) hcont.intervalIntegrable
  have hend : goldbachWeightedInnerPrimitive s (s/2)=2/s^2 := by
    unfold goldbachWeightedInnerPrimitive
    rw [show s-s/2=s/2 by ring,sub_self,zero_add]
    field_simp
  have hstart : goldbachWeightedInnerPrimitive s a=
      (-Real.log ((s-a)/a)+s/(s-a))/s^2 := by
    rw [Real.log_div hsa.ne' ha.ne']
    unfold goldbachWeightedInnerPrimitive
    ring
  rw [hFTC,hend,hstart]
  field_simp
  ring

theorem goldbach_weighted_inner_closed (r : ℝ) (_hr0 : 0≤r) (hr1 : r≤1/9) :
    goldbachWeightedInnerIntegral r=
      (((9/4:ℝ)*(1-r)-2)/((9/4:ℝ)*(1-r)-1)+
        Real.log ((9/4:ℝ)*(1-r)-1))/(1-r)^2 := by
  have hbound : (4/9:ℝ)≤(1-r)/2 := by linarith
  have he := goldbach_weighted_inner_integral (1-r) (4/9) (by norm_num) hbound
  have hratio : ((1-r)-(4/9:ℝ))/(4/9)=(9/4:ℝ)*(1-r)-1 := by ring
  unfold goldbachWeightedInnerIntegral
  rw [he,hratio]
  congr 1
  congr 1
  have hd1 : 1-r-(4/9:ℝ)≠0 := by linarith
  have hd2 : (9/4:ℝ)*(1-r)-1≠0 := by linarith
  field_simp

theorem goldbach_weighted_W_pointwise (t : ℝ) (ht : t∈Set.uIcc (2:ℝ) (9/4:ℝ)) :
    goldbachWeightedInnerIntegral (1-(4/9:ℝ)*t)/Real.sqrt (1-(4/9:ℝ)*t)=
      (81/16:ℝ)*((t-2+(t-1)*Real.log (t-1))/(t^2*(t-1)*Real.sqrt (1-t/(9/4:ℝ)))) := by
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ)≤9/4)] at ht
  have hr0 : 0≤1-(4/9:ℝ)*t := by linarith [ht.2]
  have hr1 : 1-(4/9:ℝ)*t≤1/9 := by linarith [ht.1]
  rw [goldbach_weighted_inner_closed _ hr0 hr1]
  have he : (9/4:ℝ)*(1-(1-(4/9:ℝ)*t))=t := by ring
  rw [he]
  have hs : 1-t/(9/4:ℝ)=1-(4/9:ℝ)*t := by ring
  rw [hs]
  by_cases htend : t=9/4
  · rw [htend]
    norm_num
  · have htpos : 0<t := by linarith [ht.1]
    have htm1 : t-1≠0 := by linarith [ht.1]
    have htt : t<(9/4:ℝ) := lt_of_le_of_ne ht.2 htend
    have hroot : Real.sqrt (1-(4/9:ℝ)*t)≠0 :=
      (Real.sqrt_pos.mpr (by linarith [htt])).ne'
    have hscaled : 1-(1-(4/9:ℝ)*t)≠0 := by linarith
    field_simp
    ring

theorem goldbach_weighted_W_identity :
    (∫ r in (0:ℝ)..(1/9:ℝ),goldbachWeightedInnerIntegral r/Real.sqrt r)=
      8*Real.sqrt 2*goldbachWeightedW (9/8) := by
  let F := fun r : ℝ=>goldbachWeightedInnerIntegral r/Real.sqrt r
  let G := fun t : ℝ=>(t-2+(t-1)*Real.log (t-1))/
    (t^2*(t-1)*Real.sqrt (1-t/(9/4:ℝ)))
  have hp : ∀ t∈Set.uIcc (2:ℝ) (9/4:ℝ),F (1-(4/9:ℝ)*t)=(81/16:ℝ)*G t :=
    fun t ht=>goldbach_weighted_W_pointwise t ht
  have hint : (∫ t in (2:ℝ)..(9/4:ℝ),F (1-(4/9:ℝ)*t))=
      (81/16:ℝ)*(∫ t in (2:ℝ)..(9/4:ℝ),G t) := by
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hp
  have hsub := intervalIntegral.integral_comp_sub_mul F (a:=2) (b:=9/4)
    (c:=4/9) (by norm_num) 1
  norm_num only [show (1:ℝ)-(4/9)*(9/4)=0 by norm_num,
    show (1:ℝ)-(4/9)*2=1/9 by norm_num,inv_div,smul_eq_mul] at hsub
  have hW : goldbachWeightedW (9/8)=
      (9/8:ℝ)/(4*Real.sqrt 2)*(∫ t in (2:ℝ)..(9/4:ℝ),G t) := by
    unfold goldbachWeightedW
    norm_num only [show (2:ℝ)*(9/8)=9/4 by norm_num]
    rfl
  rw [hW]
  dsimp only [F] at hint hsub
  have hroot2 : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  nlinarith only [hint,hsub]

theorem goldbach_weighted_inner_continuous :
    ContinuousOn goldbachWeightedInnerIntegral (Set.Icc (0:ℝ) (1/9:ℝ)) := by
  let F := fun r : ℝ=>
    (((9/4:ℝ)*(1-r)-2)/((9/4:ℝ)*(1-r)-1)+Real.log ((9/4:ℝ)*(1-r)-1))/(1-r)^2
  have hF : ContinuousOn F (Set.Icc (0:ℝ) (1/9:ℝ)) := by
    intro r hr
    have h₁ : (9/4:ℝ)*(1-r)-1≠0 := by linarith [hr.2]
    have h₂ : (1-r)^2≠0 := pow_ne_zero 2 (by linarith [hr.2])
    apply ContinuousAt.continuousWithinAt
    dsimp only [F]
    fun_prop
  apply hF.congr
  intro r hr
  exact goldbach_weighted_inner_closed r hr.1 hr.2

theorem goldbach_weighted_inner_nonneg (r : ℝ) (hr : r≤1/9) :
    0≤goldbachWeightedInnerIntegral r := by
  unfold goldbachWeightedInnerIntegral
  rw [intervalIntegral.integral_of_le (show (4/9:ℝ)≤(1-r)/2 by linarith)]
  apply setIntegral_nonneg measurableSet_Ioc
  intro v hv
  exact div_nonneg (by norm_num) (mul_nonneg (by linarith [hv.1] : 0≤v) (sq_nonneg _))

theorem goldbach_weighted_outer_integrable :
    IntervalIntegrable (fun r : ℝ=>goldbachWeightedInnerIntegral r/Real.sqrt r) volume 0 (1/9) := by
  have hJc : ContinuousOn goldbachWeightedInnerIntegral (Set.uIcc (0:ℝ) (1/9:ℝ)) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1/9)]
    exact goldbach_weighted_inner_continuous
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=(1/9:ℝ))
    (by norm_num : (-1:ℝ)< -(1/2:ℝ))).mul_continuousOn hJc
  have his := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1/9)).mp hi
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1/9)).mpr
  apply his.congr_fun _ measurableSet_Icc
  intro r hr
  dsimp only
  rw [Real.sqrt_eq_rpow,Real.rpow_neg hr.1]
  ring

theorem goldbach_weighted_W_integrable :
    IntervalIntegrable (fun t : ℝ=>(t-2+(t-1)*Real.log (t-1))/
      (t^2*(t-1)*Real.sqrt (1-t/(9/4:ℝ)))) volume 2 (9/4) := by
  have hI := goldbach_weighted_outer_integrable.comp_sub_left 1
  have hcomp := hI.comp_mul_left (c:=(4/9:ℝ))
  norm_num at hcomp
  have hscaled := hcomp.symm.const_mul (16/81:ℝ)
  have hset := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (2:ℝ)≤9/4)).mp hscaled
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (2:ℝ)≤9/4)).mpr
  apply hset.congr_fun _ measurableSet_Icc
  intro t ht
  have hh := goldbach_weighted_W_pointwise t (by
    simpa only [Set.uIcc_of_le (by norm_num : (2:ℝ)≤9/4)] using ht)
  dsimp only
  nlinarith only [hh]

theorem goldbach_weighted_W_nonneg : 0≤goldbachWeightedW (9/8) := by
  have hi : 0≤∫ r in (0:ℝ)..(1/9:ℝ),goldbachWeightedInnerIntegral r/Real.sqrt r := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/9)]
    apply setIntegral_nonneg measurableSet_Ioc
    intro r hr
    exact div_nonneg (goldbach_weighted_inner_nonneg r hr.2) (Real.sqrt_nonneg r)
  rw [goldbach_weighted_W_identity] at hi
  exact nonneg_of_mul_nonneg_right hi (by positivity : 0<8*Real.sqrt (2:ℝ))

end PrimeSquares
