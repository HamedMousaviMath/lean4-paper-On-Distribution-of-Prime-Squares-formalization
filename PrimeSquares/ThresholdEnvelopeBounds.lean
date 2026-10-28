import PrimeSquares.PrimeFactorThresholdBudget
import PrimeSquares.OrliczGrowth

open Filter Topology
namespace PrimeSquares

theorem gaussThresholdSlope_tendsto_zero :
    Tendsto gaussThresholdSlope atTop (𝓝 0) := by
  have h₁ := Real.tendsto_sqrt_atTop.inv_tendsto_atTop.mul
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h₂ := (hi.mul_const (Real.log 2)⁻¹).const_mul 4
  have h₁' : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹*(Real.log y)⁻¹) atTop (𝓝 0) := by
    simpa using h₁
  have h₂' : Tendsto (fun y : ℝ => 4*(y⁻¹*(Real.log 2)⁻¹)) atTop (𝓝 0) := by
    simpa using h₂
  change Tendsto (fun y : ℝ => (Real.sqrt y*Real.log y)⁻¹+4*(y⁻¹*(Real.log 2)⁻¹)) atTop (𝓝 0)
  simpa only [mul_inv_rev,mul_comm,add_zero] using h₁'.add h₂'

theorem gaussThresholdSlope_eventually_quarter :
    ∀ᶠ y : ℝ in atTop,0 ≤ gaussThresholdSlope y ∧ gaussThresholdSlope y ≤ 1/4 := by
  have h := gaussThresholdSlope_tendsto_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4))
  filter_upwards [h,eventually_ge_atTop (2 : ℝ)] with y hy h2
  exact ⟨gaussThresholdSlope_nonneg h2,hy.le⟩

theorem gaussAnalyticMajorant_regularized_ratio_tendsto (H : PrimeAsymptoticInputs) :
    Tendsto (fun y : ℝ => gaussAnalyticMajorant y/orliczWeight (1/2) y) atTop (𝓝 2) := by
  have hi : Tendsto (fun y : ℝ => 2/Real.log y) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop 2
  have hf : Tendsto (fun y : ℝ => 1+2/Real.log y) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hi
  have h := (gaussAnalyticMajorant_ratio_tendsto H).mul hf
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hl : Real.log y ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hd : 2+Real.log y ≠ 0 := by have := Real.log_nonneg (by linarith : 1 ≤ y);linarith
  dsimp [gaussAsymptoticScale,orliczWeight]
  rw [←Real.sqrt_eq_rpow]
  field_simp
  ring

theorem gaussAnalyticMajorant_regularized_eventually (H : PrimeAsymptoticInputs)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop,gaussAnalyticMajorant y ≤ (2+ε)*orliczWeight (1/2) y := by
  have h := (gaussAnalyticMajorant_regularized_ratio_tendsto H).eventually
    (eventually_lt_nhds (by linarith : (2 : ℝ) < 2+ε))
  filter_upwards [h,eventually_ge_atTop (2 : ℝ)] with y hy h2
  exact (div_le_iff₀ (orliczWeight_pos (1/2) h2)).mp hy.le

theorem conductorRho_threshold_small (q : ℕ) (hq : 0 < q) {Q : ℝ}
    (_hQ : 0 < Q) (hL : 2 ≤ Real.log Q) (hqQ : (q : ℝ) ≤ Q) :
    conductorRho q ≤ Real.exp (gaussAnalyticMajorant (Real.log Q)) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Real.log (q : ℝ)-Real.log Q ≤ 0 := sub_nonpos.mpr (Real.log_le_log hqp hqQ)
  have he : Real.exp (gaussThresholdSlope (Real.log Q)*(Real.log q-Real.log Q)) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (mul_nonpos_of_nonneg_of_nonpos (gaussThresholdSlope_nonneg hL) hl)
  exact (conductorRho_exp_threshold q hq hL).trans
    ((mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _))

theorem conductorRho_threshold_large (q : ℕ) (hq : 0 < q) {Q : ℝ}
    (hQ : 0 < Q) (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (hQq : Q ≤ (q : ℝ)) :
    conductorRho q ≤ Real.exp (gaussAnalyticMajorant (Real.log Q))*((q : ℝ)/Q)^(1/4 : ℝ) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (q : ℝ)-Real.log Q := sub_nonneg.mpr (Real.log_le_log hQ hQq)
  have he : Real.exp (gaussThresholdSlope (Real.log Q)*(Real.log q-Real.log Q)) ≤
      ((q : ℝ)/Q)^(1/4 : ℝ) := by
    rw [Real.rpow_def_of_pos (div_pos hqp hQ),Real.log_div hqp.ne' hQ.ne']
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hSlope hl]
  exact (conductorRho_exp_threshold q hq hL).trans
    (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

end PrimeSquares
