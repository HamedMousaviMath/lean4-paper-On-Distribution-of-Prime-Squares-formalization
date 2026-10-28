import PrimeSquares.GoldbachWeightedIntegralConstant
import PrimeSquares.GoldbachWeightedLogComparisons

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_inner_linear_upper (r : ℝ) (hr : r∈Set.Icc (0:ℝ) (1/9)) :
    goldbachWeightedInnerIntegral r≤(729/128:ℝ)*(1/9-r) := by
  have hab : (4/9:ℝ)≤(1-r)/2 := by linarith [hr.2]
  have hcont : ContinuousOn (fun v : ℝ=>1/(v*(1-r-v)^2)) (Set.uIcc (4/9:ℝ) ((1-r)/2)) := by
    rw [Set.uIcc_of_le hab]
    intro v hv
    have hv0 : v≠0 := by linarith [hv.1]
    have hs0 : 1-r-v≠0 := by linarith [hv.2,hr.2]
    have hden : v*(1-r-v)^2≠0 := mul_ne_zero hv0 (pow_ne_zero 2 hs0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hbound : ∀ v∈Set.Icc (4/9:ℝ) ((1-r)/2),1/(v*(1-r-v)^2)≤(729/64:ℝ) := by
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have hs : (4/9:ℝ)≤1-r-v := by linarith [hv.2,hr.2]
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4/9) hs 2
    have hp := mul_le_mul (show (4/9:ℝ)≤v from hv.1) hsq (by norm_num) hv0.le
    have hd : 0<v*(1-r-v)^2 := by positivity
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hp]
  have hi := intervalIntegral.integral_mono_on hab hcont.intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>(729/64:ℝ)) volume (4/9) ((1-r)/2)) hbound
  unfold goldbachWeightedInnerIntegral
  apply hi.trans_eq
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem goldbach_weighted_W_rational_upper :
    8*Real.sqrt 2*goldbachWeightedW (9/8)≤(9/32:ℝ) := by
  let g := fun r : ℝ=>(729/128:ℝ)*((1/9:ℝ)*r^(-(1/2:ℝ))-r^(1/2:ℝ))
  have hneg := intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=(1/9:ℝ))
    (by norm_num : (-1:ℝ)< -(1/2:ℝ))
  have hpos := intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=(1/9:ℝ))
    (by norm_num : (-1:ℝ)< (1/2:ℝ))
  have hg : IntervalIntegrable g volume 0 (1/9) := (hneg.const_mul (1/9:ℝ)).sub hpos |>.const_mul _
  have hp (r : ℝ) (hr : r∈Set.Icc (0:ℝ) (1/9)) :
      goldbachWeightedInnerIntegral r/Real.sqrt r≤g r := by
    by_cases hzero : r=0
    · subst r;simp [g]
    have hrpos : 0<r := lt_of_le_of_ne hr.1 (Ne.symm hzero)
    have hspos := Real.sqrt_pos.mpr hrpos
    have hs : (Real.sqrt r)^2=r := Real.sq_sqrt hr.1
    have hpow : r^(-(1/2:ℝ))=(Real.sqrt r)⁻¹ := by
      rw [Real.rpow_neg hr.1,Real.sqrt_eq_rpow]
    have h := div_le_div_of_nonneg_right (goldbach_weighted_inner_linear_upper r hr) hspos.le
    apply h.trans_eq
    dsimp only [g]
    rw [hpow,←Real.sqrt_eq_rpow]
    field_simp
    nlinarith only [hs]
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1/9)
    goldbach_weighted_outer_integrable hg hp
  rw [goldbach_weighted_W_identity] at hi
  have hhalf : (1/9:ℝ)^(1/2:ℝ)=1/3 := by
    rw [←Real.sqrt_eq_rpow]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  have hthree : (1/9:ℝ)^(3/2:ℝ)=1/27 := by
    rw [show (3/2:ℝ)=1/2+1 by norm_num,Real.rpow_add (by norm_num),hhalf,Real.rpow_one]
    norm_num
  have he : (∫ r in (0:ℝ)..(1/9:ℝ),g r)=9/32 := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hneg.const_mul _) hpos,intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ))),
      integral_rpow (Or.inl (by norm_num : (-1:ℝ)< (1/2:ℝ)))]
    norm_num [hhalf,hthree]
  exact hi.trans_eq he

noncomputable def goldbachSieveLowerValue : ℝ :=
  Real.sqrt (8*Real.exp Real.eulerMascheroniConstant/(9*Real.pi))*Real.log 2

theorem goldbach_sieve_numerical_comparison :
    0<goldbachSieveLowerValue-
      goldbachWeightedUpperConstant (9/8)*Real.exp Real.eulerMascheroniConstant*
        goldbachWeightedW (9/8) := by
  let q := Real.exp (Real.eulerMascheroniConstant/2)/Real.sqrt Real.pi
  have hq : 0<q := div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have h2 : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hl : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢;exact h
  have hlower : goldbachSieveLowerValue=q*(2*Real.sqrt 2/3)*Real.log 2 := by
    have he : Real.exp Real.eulerMascheroniConstant=(Real.exp (Real.eulerMascheroniConstant/2))^2 := by
      rw [←Real.exp_nat_mul];congr 1;ring
    unfold goldbachSieveLowerValue
    rw [he,Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ)≤8),
      Real.sqrt_sq (Real.exp_pos _).le,Real.sqrt_mul (by norm_num : (0:ℝ)≤9)]
    have hs4 : Real.sqrt (4:ℝ)=2 := by norm_num [Real.sqrt_eq_iff_mul_self_eq]
    have hs9 : Real.sqrt (9:ℝ)=3 := by norm_num [Real.sqrt_eq_iff_mul_self_eq]
    have hs8 : Real.sqrt (8:ℝ)=2*Real.sqrt 2 := by
      rw [show (8:ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num),hs4]
    rw [hs8,hs9]
    dsimp only [q]
    ring
  have hupper : goldbachWeightedUpperConstant (9/8)*Real.exp Real.eulerMascheroniConstant*
      goldbachWeightedW (9/8)≤(3/8:ℝ)*q := by
    have hnorm := goldbach_weighted_upper_constant_normalization (9/8) (by norm_num)
    have hsα : Real.sqrt (9/8:ℝ)=3/(2*Real.sqrt 2) := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
      field_simp
      nlinarith only [hs2]
    have he : Real.exp (-Real.eulerMascheroniConstant/2)*Real.exp Real.eulerMascheroniConstant=
        Real.exp (Real.eulerMascheroniConstant/2) := by rw [←Real.exp_add];congr 1;ring
    have hnorm' := congrArg (fun x : ℝ=>x*Real.exp Real.eulerMascheroniConstant) hnorm
    rw [hsα] at hnorm'
    dsimp only [goldbachHalfMeanConstant] at hnorm'
    have heq : goldbachWeightedUpperConstant (9/8)*Real.exp Real.eulerMascheroniConstant=
        q*(32*Real.sqrt 2/3) := by
      rw [show 48*(Real.exp (-Real.eulerMascheroniConstant/2)/Real.sqrt Real.pi)*
        Real.exp Real.eulerMascheroniConstant=48*q by dsimp [q];calc
        _=48*(Real.exp (-Real.eulerMascheroniConstant/2)*Real.exp Real.eulerMascheroniConstant)/Real.sqrt Real.pi := by ring
        _=_ := by rw [he];ring] at hnorm'
      field_simp at hnorm' ⊢
      nlinarith only [hnorm',hs2]
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left goldbach_weighted_W_rational_upper hq.le
    nlinarith only [hh]
  rw [hlower]
  have hs : (9/8:ℝ)<Real.sqrt 2 := by
    nlinarith only [hs2,h2]
  have hlow := mul_le_mul_of_nonneg_left hl (mul_nonneg hq.le (by positivity : 0≤2*Real.sqrt 2/3))
  have hstrict := mul_pos hq (show 0<Real.sqrt 2/3-3/8 by linarith)
  nlinarith only [hupper,hlow,hstrict]

theorem goldbach_normalized_sieve_comparison (f F : ℝ→ℝ)
    (hf : f (9/8)=goldbachSieveLowerValue)
    (hF : F 2=Real.exp Real.eulerMascheroniConstant) :
    0<f (9/8)-goldbachWeightedUpperConstant (9/8)*F 2*goldbachWeightedW (9/8) := by
  rw [hf,hF]
  exact goldbach_sieve_numerical_comparison

end PrimeSquares
