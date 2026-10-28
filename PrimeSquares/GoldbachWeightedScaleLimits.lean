import PrimeSquares.GoldbachWeightedMeanCutoffs
import PrimeSquares.GoldbachWeightedIntegralConstant
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_weighted_log_power_sqrt_limit (j : ℕ) :
    Tendsto (fun L : ℝ=>(Real.log L)^j/Real.sqrt L) atTop (nhds 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (j:ℝ)
    (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast,Real.sqrt_eq_rpow] using hh

theorem goldbach_weighted_sqrt_log_inverse_limit (C : ℝ) (hC : 0<C) :
    Tendsto (fun L : ℝ=>1/Real.sqrt (C*Real.log L)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop hC))

theorem goldbach_weighted_main_coefficient_limit (C K δ K₁ ε : ℝ) (hC : 0<C) :
    Tendsto (fun L : ℝ=>(goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/(C*Real.log L))*
      Real.sqrt (1+Real.log 2/Real.sqrt L)*goldbachWeightedW (9/8))
      atTop (nhds ((goldbachHalfMeanConstant+K*ε^δ)*goldbachWeightedW (9/8))) := by
  have hOne : Tendsto (fun _ : ℝ=>(1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hR : Tendsto (fun L : ℝ=>K₁/(C*Real.log L)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.const_mul_atTop hC)
  have hL : Tendsto (fun L : ℝ=>Real.log 2/Real.sqrt L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h₁ := (hOne.add hR).const_mul (goldbachHalfMeanConstant+K*ε^δ)
  have h₂ := (hOne.add hL).sqrt
  simpa using (h₁.mul h₂).mul_const (goldbachWeightedW (9/8))

theorem goldbach_weighted_small_coefficient_limit (C P A : ℝ) (hC : 0<C)
    (hP : 0≤P) (_hA : 0≤A) :
    Tendsto (fun L : ℝ=>2*P*Real.sqrt (C*Real.log L)*(C*Real.log L)^6/Real.sqrt L+
      2*A*(1+Real.sqrt L)/(Real.sqrt (C*Real.log L)*Real.sqrt L)) atTop (nhds 0) := by
  have hmajor : Tendsto (fun L : ℝ=>2*P*(C+1)*C^6*((Real.log L)^7/Real.sqrt L)) atTop (nhds 0) := by
    simpa using (goldbach_weighted_log_power_sqrt_limit 7).const_mul (2*P*(C+1)*C^6)
  have hfirst : Tendsto (fun L : ℝ=>2*P*Real.sqrt (C*Real.log L)*(C*Real.log L)^6/Real.sqrt L)
      atTop (nhds 0) := by
    apply squeeze_zero' _ _ hmajor
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
      have hlog : 1≤Real.log L := by
        have hh := Real.log_le_log (Real.exp_pos 1) hL
        rwa [Real.log_exp] at hh
      positivity
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
      have hlog : 1≤Real.log L := by
        have hh := Real.log_le_log (Real.exp_pos 1) hL
        rwa [Real.log_exp] at hh
      have hs : Real.sqrt (C*Real.log L)≤(C+1)*Real.log L := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · have hsq : Real.log L≤(Real.log L)^2 := by nlinarith
          have hCbig : C≤(C+1)^2 := by nlinarith
          have hh := mul_le_mul hCbig hsq (by linarith) (by positivity : (0:ℝ)≤(C+1)^2)
          nlinarith only [hh]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs (by positivity : 0≤2*P*(C*Real.log L)^6))
        (Real.sqrt_nonneg L)
      convert hh using 1 <;> ring
  have hInv : Tendsto (fun L : ℝ=>1/Real.sqrt L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hsecond : Tendsto (fun L : ℝ=>2*A*(1+Real.sqrt L)/
      (Real.sqrt (C*Real.log L)*Real.sqrt L)) atTop (nhds 0) := by
    have hOne : Tendsto (fun _ : ℝ=>(1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hh := ((hOne.add hInv).mul
      (goldbach_weighted_sqrt_log_inverse_limit C hC)).const_mul (2*A)
    apply (show Tendsto (fun L : ℝ=>2*A*((1+1/Real.sqrt L)*(1/Real.sqrt (C*Real.log L))))
      atTop (nhds 0) by simpa using hh).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with L hL
    have hs : Real.sqrt L≠0 := (Real.sqrt_pos.mpr (by linarith : 0<L)).ne'
    have hlog : 0<Real.log L := Real.log_pos hL
    have hsR : Real.sqrt (C*Real.log L)≠0 := (Real.sqrt_pos.mpr (mul_pos hC hlog)).ne'
    field_simp
    ring
  simpa only [zero_add] using hfirst.add hsecond

theorem goldbach_weighted_endpoint_coefficient_limit (C K K₁ δ ε K₀ : ℝ) (hC : 0<C) :
    Tendsto (fun L : ℝ=>6*(K₀+1)*(goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/(C*Real.log L))/
      (Real.sqrt (Real.sqrt L)*Real.sqrt L)) atTop (nhds 0) := by
  have hInv : Tendsto (fun L : ℝ=>1/Real.sqrt (Real.sqrt L)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop)
  have hInv₂ : Tendsto (fun L : ℝ=>1/Real.sqrt L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hR : Tendsto (fun L : ℝ=>K₁/(C*Real.log L)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.const_mul_atTop hC)
  have hOne : Tendsto (fun _ : ℝ=>(1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := (((hOne.add hR).mul hInv).mul hInv₂).const_mul
    (6*(K₀+1)*(goldbachHalfMeanConstant+K*ε^δ))
  convert (show Tendsto (fun L : ℝ=>6*(K₀+1)*(goldbachHalfMeanConstant+K*ε^δ)*
    (((1+K₁/(C*Real.log L))*(1/Real.sqrt (Real.sqrt L)))*(1/Real.sqrt L))) atTop (nhds 0)
    by simpa using hh) using 1
  ext L
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
