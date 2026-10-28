import PrimeSquares.NearOneGaugeComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrimeSquares

theorem nearOne_log_affine {a : ℝ} (ha : 0<a) {v : ℝ} (hv : 0≤v) :
    Real.log (Real.exp 1+v) ≤ a*v + Real.log (1/a)+a*Real.exp 1-1 := by
  have he : 0<Real.exp 1+v := by positivity
  have h := Real.log_le_sub_one_of_pos (mul_pos ha he)
  rw [Real.log_mul ha.ne' he.ne'] at h
  rw [one_div,Real.log_inv]
  nlinarith

theorem root_product_absorption {v H e C : ℝ} (hv : 0≤v) (hH : 0≤H)
    (he : 0<e) (hC : 0<C) {B : ℝ} (hB : 0≤B)
    (hbound : B ≤ e^2/(16*C^2)*v+H) :
    C*Real.sqrt (v*B) ≤ e*v/2+2*C^2*H/e := by
  have hs0 := Real.sqrt_nonneg (v*B)
  have hs := Real.sq_sqrt (mul_nonneg hv hB)
  have hsq : (C*Real.sqrt (v*B))^2 ≤ e^2*v^2/16+C^2*H*v := by
    have h := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg C) hv)
    have heq : C^2*v*(e^2/(16*C^2)*v+H)=e^2*v^2/16+C^2*H*v := by
      field_simp
    rw [heq] at h
    nlinarith
  have he0 : e ≠ 0 := ne_of_gt he
  have hleft : 0≤C*Real.sqrt (v*B) := mul_nonneg hC.le hs0
  have hright : 0≤e*v/2+2*C^2*H/e := by positivity
  have hdiff : e^2*v^2/16+C^2*H*v ≤ (e*v/2+2*C^2*H/e)^2 := by
    have h : 0≤3*e^2*v^2/16+4*C^4*H^2/e^2 := by positivity
    field_simp at h ⊢
    nlinarith [sq_nonneg (e*v)]
  nlinarith

noncomputable def nearOneGrowthConstant (C : ℝ) : ℝ :=
  2*C^2*(Real.exp 1+Real.log (16*C^2)+2)

theorem nearOneGrowthConstant_pos {C : ℝ} (hC : 1≤C) : 0<nearOneGrowthConstant C := by
  have hl : 0≤Real.log (16*C^2) := Real.log_nonneg (by nlinarith [sq_nonneg (C-1)])
  unfold nearOneGrowthConstant
  positivity

theorem nearOneCore_quantitative {C e v : ℝ} (hC : 1≤C) (he : 0<e) (he1 : e≤1) (hv : 1≤v) :
    C*nearOneCore v ≤ e*v/2+nearOneGrowthConstant C/e*Real.log (Real.exp 1/e) := by
  let a := e^2/(16*C^2)
  let L := Real.log (Real.exp 1/e)
  let H := (Real.exp 1+Real.log (16*C^2)+2)*L
  have hC0 : 0<C := by linarith
  have ha : 0<a := by dsimp [a]; positivity
  have ha1 : a≤1 := by
    dsimp [a]
    apply (div_le_one (by positivity : 0<16*C^2)).mpr
    nlinarith [sq_nonneg (C-1),sq_nonneg e]
  have hlogE : Real.log e≤0 := Real.log_nonpos he.le he1
  have hL : L=1-Real.log e := by dsimp [L];rw [Real.log_div (Real.exp_pos 1).ne' he.ne',Real.log_exp]
  have hL1 : 1≤L := by linarith
  have hlogC : 0≤Real.log (16*C^2) := Real.log_nonneg (by nlinarith [sq_nonneg (C-1)])
  have hH : 0≤H := by dsimp [H]; positivity
  have hi : Real.log (1/a)=Real.log (16*C^2)-2*Real.log e := by
    have heq : 1/a=(16*C^2)/(e^2) := by dsimp [a];field_simp
    rw [heq,Real.log_div (by positivity : 16*C^2≠0) (by positivity : e^2≠0),Real.log_pow]
    ring
  have hb := nearOne_log_affine ha (show 0≤v by linarith)
  have hconst : Real.log (1/a)+a*Real.exp 1-1 ≤ H := by
    rw [hi]
    have haE := mul_le_mul_of_nonneg_right ha1 (Real.exp_pos (1 : ℝ)).le
    have hx := mul_nonneg (show 0≤Real.exp 1+Real.log (16*C^2) by positivity) (show 0≤L-1 by linarith)
    dsimp [H] at *
    nlinarith
  have hB0 : 0≤Real.log (Real.exp 1+v) := by linarith [(nearOne_innerLog_bounds hv).1]
  have h := root_product_absorption (show 0≤v by linarith) hH he hC0 hB0
    (show Real.log (Real.exp 1+v) ≤ e^2/(16*C^2)*v+H by
      dsimp [a] at hb hconst
      linarith)
  change C*nearOneCore v ≤ _ at h
  dsimp [H,L,nearOneGrowthConstant] at *
  convert h using 1
  ring

theorem nearOneDensity_small_power {C e t : ℝ} (hC : 1≤C) (he : 0<e) (he1 : e≤1) :
    nearOneDensity C t ≤
      Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)) *
        (Real.exp 1+max 0 t)^(e/2) := by
  have hb := nearOneCore_quantitative hC he he1 (nearOneLog_one_le t)
  change C*nearOneRate t ≤ e*nearOneLog t/2+_ at hb
  unfold nearOneDensity
  rw [Real.rpow_def_of_pos (by positivity : 0<Real.exp 1+max 0 t),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [nearOneLog] at hb
  linarith

end PrimeSquares
