import PrimeSquares.NearOneGaugeMoment

open Set MeasureTheory
namespace PrimeSquares

noncomputable def nearOneMomentConstant (C C0 : ℝ) : ℝ :=
  nearOneGrowthConstant C+1+Real.log (2*C0*(1+Real.exp 1*C0))

theorem nearOne_log_reciprocal_bounds {e : ℝ} (he : 0<e) (he1 : e≤1) :
    1≤(1/e)*Real.log (Real.exp 1/e) ∧
      -Real.log e≤(1/e)*Real.log (Real.exp 1/e) := by
  have hlog : 1≤Real.log (Real.exp 1/e) := by
    rw [Real.log_div (Real.exp_pos 1).ne' he.ne',Real.log_exp]
    linarith [Real.log_nonpos he.le he1]
  have hinv : 1≤1/e := (one_le_div he).mpr he1
  have hp := one_le_mul_of_one_le_of_one_le hinv hlog
  have hL := le_mul_of_one_le_left (show 0≤Real.log (Real.exp 1/e) by linarith) hinv
  constructor
  · exact hp
  · rw [Real.log_div (Real.exp_pos 1).ne' he.ne',Real.log_exp] at hL ⊢
    linarith

theorem nearOneMoment_prefactor_one_le {C0 : ℝ} (hC0 : 1≤C0) :
    1≤2*C0*(1+Real.exp 1*C0) :=
  one_le_mul_of_one_le_of_one_le (by linarith)
    (by have h := mul_nonneg (Real.exp_pos (1 : ℝ)).le (show 0≤C0 by linarith);linarith)

theorem nearOneMomentConstant_pos {C C0 : ℝ} (hC : 1≤C) (hC0 : 1≤C0) :
    0<nearOneMomentConstant C C0 := by
  have hM := nearOneMoment_prefactor_one_le hC0
  unfold nearOneMomentConstant
  linarith [nearOneGrowthConstant_pos hC,Real.log_nonneg hM]

theorem nearOneGaugeMoment_exponential {C C0 e : ℝ} (hC : 1≤C) (hC0 : 1≤C0)
    (he : 0<e) (he1 : e≤1) :
    (∫ u : ℝ in Ioi (1/C0),nearOnePsi C u*u^(-e-2))≤
      Real.exp (nearOneMomentConstant C C0/e*Real.log (Real.exp 1/e)) := by
  have hC00 : 0<C0 := by linarith
  have ha : 0<1/C0 := by positivity
  have hp : (1/C0)^(-e/2)≤C0 := by
    have heq : (1/C0)^(-e/2)=C0^(e/2) := by
      rw [one_div,Real.inv_rpow hC00.le,show -e/2=-(e/2) by ring,Real.rpow_neg hC00.le,inv_inv]
    rw [heq]
    exact (Real.rpow_le_rpow_of_exponent_le hC0 (by linarith : e/2≤1)).trans_eq (Real.rpow_one C0)
  have h0 := nearOneGaugeMoment_bound hC ha he he1
  have h1 := mul_le_mul_of_nonneg_left hp
    (show 0≤nearOnePowerConstant C (1/C0) e*(2/e) by have h := nearOnePowerConstant_pos ha C e;positivity)
  have hbound : (∫ u : ℝ in Ioi (1/C0),nearOnePsi C u*u^(-e-2))≤
      ((2*C0*(1+Real.exp 1*C0))/e)*
        Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)) := by
    have h := h0.trans h1
    unfold nearOnePowerConstant at h
    have hi : Real.exp 1/(1/C0)=Real.exp 1*C0 := by field_simp
    rw [hi] at h
    convert h using 1
    ring
  let M := 2*C0*(1+Real.exp 1*C0)
  let T := (1/e)*Real.log (Real.exp 1/e)
  have hM : 1≤M := nearOneMoment_prefactor_one_le hC0
  have hM0 : 0<M := by linarith
  have hT := nearOne_log_reciprocal_bounds he he1
  have hlogM : 0≤Real.log M := Real.log_nonneg hM
  have hineq : Real.log M-Real.log e≤(1+Real.log M)*T := by
    have h := mul_le_mul_of_nonneg_left hT.1 hlogM
    dsimp [T]
    nlinarith [hT.2]
  have hExp : (M/e)*Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e))≤
      Real.exp (nearOneMomentConstant C C0/e*Real.log (Real.exp 1/e)) := by
    rw [←Real.exp_log (div_pos hM0 he),←Real.exp_add,Real.log_div hM0.ne' he.ne']
    apply Real.exp_le_exp.mpr
    change Real.log M-Real.log e+nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)≤
      (nearOneGrowthConstant C+1+Real.log M)/e*Real.log (Real.exp 1/e)
    dsimp [T] at hineq
    simp only [div_eq_mul_inv] at hineq ⊢
    nlinarith
  exact hbound.trans hExp

theorem nearOneGaugeMoment_source_p {C C0 p : ℝ} (hC : 1≤C) (hC0 : 1≤C0)
    (hp : 1<p) (hp2 : p≤2) :
    IntegrableOn (fun u : ℝ => nearOnePsi C u*u^(-p-1)) (Ioi (1/C0)) ∧
      (∫ u : ℝ in Ioi (1/C0),nearOnePsi C u*u^(-p-1))≤
        Real.exp (nearOneMomentConstant C C0/(p-1)*Real.log (Real.exp 1/(p-1))) := by
  have he : 0<p-1 := by linarith
  have he1 : p-1≤1 := by linarith
  have ha : 0<1/C0 := by
    have hC00 : 0<C0 := by linarith
    positivity
  have hi := nearOneGaugeMoment_integrable hC ha he he1
  have hb := nearOneGaugeMoment_exponential hC hC0 he he1
  rw [show -(p-1)-2=-p-1 by ring] at hi hb
  exact ⟨hi,hb⟩

end PrimeSquares
