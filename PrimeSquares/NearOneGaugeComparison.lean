import PrimeSquares.NearOneGauge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set MeasureTheory
namespace PrimeSquares

noncomputable def nearOneCore (v : ℝ) : ℝ := Real.sqrt (v * Real.log (Real.exp 1+v))

theorem nearOne_innerLog_bounds {v : ℝ} (hv : 1 ≤ v) :
    1 ≤ Real.log (Real.exp 1+v) ∧ Real.log (Real.exp 1+v) ≤ 2*v := by
  have he := Real.exp_pos v
  have hve : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have hee : Real.exp 1 ≤ Real.exp v := Real.exp_le_exp.mpr hv
  have hlog := Real.log_le_log (by have := Real.exp_pos (1 : ℝ); linarith : 0 < Real.exp 1+v)
    (show Real.exp 1+v ≤ 2*Real.exp v by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) he.ne', Real.log_exp] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h
  refine ⟨?_, by linarith⟩
  have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.exp 1+v by linarith)
  simpa using h

theorem nearOneCore_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    nearOneCore y ≤ nearOneCore x+2*(y-x) := by
  let Bx := Real.log (Real.exp 1+x)
  let By := Real.log (Real.exp 1+y)
  let d := y-x
  let a := Real.exp 1+x
  have hd : 0 ≤ d := sub_nonneg.mpr hxy
  have ha : 1 ≤ a := by dsimp [a]; linarith [Real.exp_pos (1 : ℝ)]
  have hxa : x ≤ a := by dsimp [a]; linarith [Real.exp_pos (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < Real.exp 1+y := by linarith [Real.exp_pos (1 : ℝ)]
  have hBx := nearOne_innerLog_bounds hx
  have hBy : Bx ≤ By := Real.log_le_log ha0 (by linarith)
  have ht := Real.log_le_sub_one_of_pos (div_pos hy0 ha0)
  rw [Real.log_div hy0.ne' ha0.ne'] at ht
  have htan : a*(By-Bx) ≤ d := by
    have he : (Real.exp 1+y)/a-1=d/a := by dsimp [d,a]; field_simp; ring
    change By-Bx ≤ (Real.exp 1+y)/a-1 at ht
    rw [he] at ht
    have h := (le_div_iff₀ ha0).mp ht
    nlinarith
  have hcoef : y ≤ (1+d)*a := by
    have h := mul_nonneg hd (sub_nonneg.mpr ha)
    dsimp [d] at *
    nlinarith
  have hdiff : y*(By-Bx) ≤ (1+d)*d := by
    calc
      _ ≤ ((1+d)*a)*(By-Bx) := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hBy)
      _ = (1+d)*(a*(By-Bx)) := by ring
      _ ≤ (1+d)*d := mul_le_mul_of_nonneg_left htan (by linarith)
  have hs0 := Real.sqrt_nonneg (x*Bx)
  have hsp := Real.sq_sqrt (show 0 ≤ x*Bx by have := hBx.1; dsimp [Bx] at *; positivity)
  have ht0 := Real.sqrt_nonneg (y*By)
  have htp := Real.sq_sqrt (show 0 ≤ y*By by
    have h : 1 ≤ By := hBx.1.trans hBy
    have hy : 0 ≤ y := by linarith
    exact mul_nonneg hy (by linarith))
  have hs1 : 1 ≤ Real.sqrt (x*Bx) := by
    have hp : 1 ≤ x*Bx := one_le_mul_of_one_le_of_one_le hx hBx.1
    nlinarith
  have hsB : Bx ≤ 2*Real.sqrt (x*Bx) := by
    have hp := mul_nonneg (show 0 ≤ Bx by linarith [hBx.1]) (sub_nonneg.mpr hBx.2)
    nlinarith
  have hquad : y*By ≤ x*Bx+d*(Bx+1)+d^2 := by dsimp [d] at *; nlinarith
  have hmain := mul_nonneg hd (show 0 ≤ 4*Real.sqrt (x*Bx)-Bx-1 by linarith)
  have hsquare : (Real.sqrt (y*By))^2 ≤ (Real.sqrt (x*Bx)+2*d)^2 := by nlinarith [sq_nonneg d]
  dsimp [nearOneCore]
  change Real.sqrt (y*By) ≤ Real.sqrt (x*Bx)+2*d
  nlinarith

theorem nearOneRate_rescale {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    nearOneRate (a*t) ≤ nearOneRate t+2*Real.log a := by
  have ha0 : 0<a := by linarith
  have hle : nearOneLog t ≤ nearOneLog (a*t) := nearOneLog_mono (by nlinarith)
  have hlog : nearOneLog (a*t) ≤ nearOneLog t+Real.log a := by
    have h := Real.log_le_log (show 0<Real.exp 1+a*t by positivity)
      (show Real.exp 1+a*t ≤ a*(Real.exp 1+t) by nlinarith [Real.exp_pos (1 : ℝ)])
    rw [Real.log_mul ha0.ne' (by positivity : Real.exp 1+t ≠ 0)] at h
    simpa [nearOneLog,max_eq_right ht,max_eq_right (mul_nonneg ha0.le ht),add_comm] using h
  have h := nearOneCore_lipschitz (nearOneLog_one_le t) hle
  change nearOneRate (a*t) ≤ nearOneRate t+2*(nearOneLog (a*t)-nearOneLog t) at h
  linarith

theorem nearOneDensity_rescale {C a t : ℝ} (hC : 0 ≤ C) (ha : 1 ≤ a) (ht : 0 ≤ t) :
    nearOneDensity C (a*t) ≤ Real.exp (2*C*Real.log a)*nearOneDensity C t := by
  rw [nearOneDensity,nearOneDensity,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (nearOneRate_rescale ha ht) hC
  nlinarith

theorem nearOnePsi_ge_half_density {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    (t/2)*nearOneDensity C (t/2) ≤ nearOnePsi C t := by
  have hhalf : 0 ≤ t/2 := by positivity
  have hab : t/2 ≤ t := by linarith
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => nearOneDensity C (t/2)) volume (t/2) t)
    ((nearOneDensity_continuous C).intervalIntegrable (t/2) t)
    (fun u hu => nearOneDensity_mono hC hu.1)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((nearOneDensity_continuous C).intervalIntegrable 0 (t/2))
    ((nearOneDensity_continuous C).intervalIntegrable (t/2) t)
  have hn := nearOnePsi_nonneg C hhalf
  simp only [intervalIntegral.integral_const,sub_eq_add_neg,smul_eq_mul] at h
  change nearOnePsi C (t/2)+(∫ u in t/2..t,nearOneDensity C u)=nearOnePsi C t at he
  linarith

theorem nearOnePsi_comparison {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    t*nearOneDensity C t ≤ (2*Real.exp (2*C*Real.log 2))*nearOnePsi C t := by
  have h := nearOneDensity_rescale hC (by norm_num : (1 : ℝ)≤2) (show 0≤t/2 by positivity)
  rw [show (2 : ℝ)*(t/2)=t by ring] at h
  have h' := mul_le_mul_of_nonneg_left h ht
  have h'' := mul_le_mul_of_nonneg_left (nearOnePsi_ge_half_density hC ht)
    (show 0≤2*Real.exp (2*C*Real.log 2) by positivity)
  nlinarith

theorem nearOnePsi_doubling {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    nearOnePsi C (2*t) ≤ (4*Real.exp (4*C*Real.log 2))*nearOnePsi C t := by
  have h1 := nearOnePsi_le_density hC (show 0≤2*t by positivity)
  have h2 := nearOneDensity_rescale hC (by norm_num : (1 : ℝ)≤2) ht
  have h3 := nearOnePsi_comparison hC ht
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0≤2*t by positivity)
  have h5 := mul_le_mul_of_nonneg_left h3 (show 0≤2*Real.exp (2*C*Real.log 2) by positivity)
  have he : Real.exp (4*C*Real.log 2)=Real.exp (2*C*Real.log 2)^2 := by
    rw [pow_two,←Real.exp_add];congr 1;ring
  rw [he]
  nlinarith

end PrimeSquares
