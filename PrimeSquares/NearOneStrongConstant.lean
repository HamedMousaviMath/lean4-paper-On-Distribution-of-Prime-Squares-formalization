import PrimeSquares.NearOneMomentExponential

set_option autoImplicit false
namespace PrimeSquares

theorem nearOneMoment_prefactor_bound {C C₀ e : ℝ} (hC₀ : 1 ≤ C₀)
    (he : 0 < e) (he1 : e ≤ 1) :
    ((2*C₀*(1+Real.exp 1*C₀))/e)*Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)) ≤
      Real.exp (nearOneMomentConstant C C₀/e*Real.log (Real.exp 1/e)) := by
  let M := 2*C₀*(1+Real.exp 1*C₀)
  let T := (1/e)*Real.log (Real.exp 1/e)
  have hM : 1 ≤ M := nearOneMoment_prefactor_one_le hC₀
  have hM0 : 0 < M := by linarith
  have hT := nearOne_log_reciprocal_bounds he he1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hineq : Real.log M-Real.log e ≤ (1+Real.log M)*T := by
    have h := mul_le_mul_of_nonneg_left hT.1 hlogM
    dsimp [T]
    nlinarith [hT.2]
  change (M/e)*Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)) ≤ _
  rw [←Real.exp_log (div_pos hM0 he), ←Real.exp_add, Real.log_div hM0.ne' he.ne']
  apply Real.exp_le_exp.mpr
  change Real.log M-Real.log e+nearOneGrowthConstant C/e*Real.log (Real.exp 1/e) ≤
    (nearOneGrowthConstant C+1+Real.log M)/e*Real.log (Real.exp 1/e)
  dsimp [T] at hineq
  simp only [div_eq_mul_inv] at hineq ⊢
  nlinarith

noncomputable def nearOneStrongConstant (C C₀ K : ℝ) : ℝ :=
  nearOneMomentConstant C C₀+Real.log (2*K)+1

theorem nearOneStrongConstant_pos {C C₀ K : ℝ} (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (hK : 1 ≤ K) :
    0 < nearOneStrongConstant C C₀ K := by
  have hm := nearOneMomentConstant_pos hC hC₀
  have hlog := Real.log_nonneg (show 1 ≤ 2*K by linarith)
  unfold nearOneStrongConstant
  linarith

theorem nearOneStrong_power_budget {C C₀ K p : ℝ} (hC₀ : 1 ≤ C₀) (hK : 1 ≤ K)
    (hp : 1 < p) (hp2 : p ≤ 2) :
    K*nearOnePowerConstant C (1/C₀) (p-1)*p*
      (C₀^(p-(1+(p-1)/2))/(p-(1+(p-1)/2))) ≤
      Real.exp (nearOneStrongConstant C C₀ K/(p-1)*Real.log (Real.exp 1/(p-1))) := by
  have he : 0 < p-1 := by linarith
  have he1 : p-1 ≤ 1 := by linarith
  have hC₀0 : 0 < C₀ := by linarith
  have hK0 : 0 < K := by linarith
  have hd : p-(1+(p-1)/2) = (p-1)/2 := by ring
  have hpow : C₀^((p-1)/2) ≤ C₀ :=
    (Real.rpow_le_rpow_of_exponent_le hC₀ (by linarith : (p-1)/2 ≤ 1)).trans_eq (Real.rpow_one C₀)
  let M := 2*C₀*(1+Real.exp 1*C₀)
  let L := Real.log (Real.exp 1/(p-1))
  have hbase : K*nearOnePowerConstant C (1/C₀) (p-1)*p*
      (C₀^(p-(1+(p-1)/2))/(p-(1+(p-1)/2))) ≤
      (2*K)*((M/(p-1))*Real.exp (nearOneGrowthConstant C/(p-1)*L)) := by
    rw [hd]
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0 ≤ K*nearOnePowerConstant C (1/C₀) (p-1)*p/((p-1)/2) by
      have h := nearOnePowerConstant_pos (by positivity : 0 < 1/C₀) C (p-1)
      positivity)
    have h2 := mul_le_mul_of_nonneg_left hp2
      (show 0 ≤ K*nearOnePowerConstant C (1/C₀) (p-1)*C₀/((p-1)/2) by
        have h := nearOnePowerConstant_pos (by positivity : 0 < 1/C₀) C (p-1)
        positivity)
    have hi : Real.exp 1/(1/C₀) = Real.exp 1*C₀ := by field_simp
    calc
      _ ≤ K*nearOnePowerConstant C (1/C₀) (p-1)*p/((p-1)/2)*C₀ := by
        convert h1 using 1; ring
      _ = K*nearOnePowerConstant C (1/C₀) (p-1)*C₀/((p-1)/2)*p := by ring
      _ ≤ K*nearOnePowerConstant C (1/C₀) (p-1)*C₀/((p-1)/2)*2 := h2
      _ = _ := by
        unfold nearOnePowerConstant
        rw [hi]
        dsimp [M, L]
        field_simp

  have hpre := nearOneMoment_prefactor_bound (C := C) hC₀ he he1
  have hfinal : (2*K)*Real.exp (nearOneMomentConstant C C₀/(p-1)*L) ≤
      Real.exp (nearOneStrongConstant C C₀ K/(p-1)*L) := by
    let T := (1/(p-1))*L
    have hT : 1 ≤ T := (nearOne_log_reciprocal_bounds he he1).1
    have hlog : 0 ≤ Real.log (2*K) := Real.log_nonneg (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hT hlog
    have hineq : Real.log (2*K)+nearOneMomentConstant C C₀*T ≤
        (nearOneMomentConstant C C₀+Real.log (2*K)+1)*T := by nlinarith
    rw [←Real.exp_log (by positivity : 0 < 2*K), ←Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold nearOneStrongConstant
    convert hineq using 1 <;> dsimp [T] <;> ring

  exact hbase.trans ((mul_le_mul_of_nonneg_left hpre (by positivity : 0 ≤ 2*K)).trans hfinal)

end PrimeSquares
