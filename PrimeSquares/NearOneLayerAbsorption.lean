import PrimeSquares.NearOneGaugeComparison
import Mathlib.Tactic.GCongr

open Set MeasureTheory
namespace PrimeSquares

theorem nearOneDensity_coefficient_mono {C D : ℝ} (hCD : C≤D) (t : ℝ) :
    nearOneDensity C t≤nearOneDensity D t :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCD (nearOneRate_nonneg t))

theorem nearOnePsi_coefficient_mono {C D t : ℝ} (hCD : C≤D) (ht : 0≤t) :
    nearOnePsi C t≤nearOnePsi D t :=
  intervalIntegral.integral_mono_on ht ((nearOneDensity_continuous C).intervalIntegrable 0 t)
    ((nearOneDensity_continuous D).intervalIntegrable 0 t) (fun u _ => nearOneDensity_coefficient_mono hCD u)

theorem nearOneRate_ge_sqrt_log (t : ℝ) : Real.sqrt (nearOneLog t)≤nearOneRate t := by
  apply Real.sqrt_le_sqrt
  have h := (nearOne_innerLog_bounds (nearOneLog_one_le t)).1
  exact le_mul_of_one_le_right (by linarith [nearOneLog_one_le t]) h

theorem log_le_two_sqrt {v : ℝ} (hv : 1≤v) : Real.log v≤2*Real.sqrt v := by
  have hv0 : 0<v := by linarith
  have hs := Real.sqrt_pos.mpr hv0
  have h := Real.log_le_sub_one_of_pos hs
  have he : Real.log v=2*Real.log (Real.sqrt v) := by
    conv_lhs => rw [←Real.sq_sqrt hv0.le]
    rw [Real.log_pow]
    norm_num
  rw [he]
  linarith

theorem nearOnePsi_variable_rescale {C a t L d : ℝ} (hC : 0≤C) (ha : 1≤a)
    (ht : 0≤t) (_hL : 0≤L) (hd : 0≤d)
    (hlog : Real.log a≤L+d*nearOneRate t) :
    nearOnePsi C (a*t)≤
      (2*Real.exp ((1+2*C)*L+2*(C+(1+2*C)*d)*Real.log 2))*
        nearOnePsi (C+(1+2*C)*d) t := by
  let D := C+(1+2*C)*d
  have hD : 0≤D := by dsimp [D];positivity
  have h1 := nearOnePsi_le_density hC (mul_nonneg (by linarith : 0≤a) ht)
  have h2 := nearOneDensity_rescale hC ha ht
  have hstep := mul_le_mul_of_nonneg_left h2 (show 0≤a*t by positivity)
  have hexp : a*Real.exp (2*C*Real.log a)*nearOneDensity C t ≤
      Real.exp ((1+2*C)*L)*nearOneDensity D t := by
    conv_lhs => lhs;lhs;rw [←Real.exp_log (by linarith : 0<a)]
    rw [nearOneDensity,nearOneDensity,←Real.exp_add,←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hlog (show 0≤1+2*C by positivity)
    dsimp [D]
    nlinarith
  have hexpt := mul_le_mul_of_nonneg_right hexp ht
  have h3 := mul_le_mul_of_nonneg_left (nearOnePsi_comparison hD ht) (Real.exp_pos ((1+2*C)*L)).le
  have he : Real.exp ((1+2*C)*L)*(2*Real.exp (2*D*Real.log 2))=
      2*Real.exp ((1+2*C)*L+2*D*Real.log 2) := by rw [Real.exp_add];ring
  rw [←he]
  change nearOnePsi C (a*t)≤_ * nearOnePsi D t
  nlinarith

theorem nearOnePsi_log_polynomial {C a t D : ℝ} (hC : 0≤C) (ha : 1≤a)
    (ht : 0≤t) (hD : 1≤D) (haD : a≤D*(nearOneLog t)^2) :
    nearOnePsi C (a*t)≤
      (2*Real.exp ((1+2*C)*Real.log D+2*(9*C+4)*Real.log 2))*nearOnePsi (9*C+4) t := by
  have hlog : Real.log a≤Real.log D+4*nearOneRate t := by
    have hl := Real.log_le_log (by linarith : 0<a) haD
    rw [Real.log_mul (by linarith : D≠0) (by have := nearOneLog_one_le t;positivity),Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have h := (log_le_two_sqrt (nearOneLog_one_le t)).trans
      (mul_le_mul_of_nonneg_left (nearOneRate_ge_sqrt_log t) (by norm_num : (0 : ℝ)≤2))
    linarith
  have h := nearOnePsi_variable_rescale hC ha ht (Real.log_nonneg hD)
    (by norm_num : (0 : ℝ)≤4) hlog
  have he : C+(1+2*C)*4=9*C+4 := by ring
  rw [he] at h
  exact h

end PrimeSquares
