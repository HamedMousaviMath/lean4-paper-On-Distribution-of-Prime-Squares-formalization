import PrimeSquares.GoldbachPresieveClassicalInputs
import PrimeSquares.LogPowerAbsorption

set_option autoImplicit false
open Filter
namespace PrimeSquares

noncomputable def goldbachLowerSieveLevel (B N : ℝ) : ℝ :=
  N / (24 * (Real.log N)^B)

noncomputable def goldbachLowerOuterLevel (B N : ℝ) : ℝ :=
  goldbachLowerSieveLevel B N / Real.exp ((Real.log (Real.log N))^3)

noncomputable def goldbachLowerSiftingLimit (N : ℝ) : ℝ := N^((8:ℝ)/9)

theorem goldbach_lower_outer_level_pos (B N : ℝ) (hN : 1<N) :
    0 < goldbachLowerOuterLevel B N := by
  unfold goldbachLowerOuterLevel goldbachLowerSieveLevel
  exact div_pos (div_pos (by linarith) (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (Real.log_pos hN) B))) (Real.exp_pos _)

theorem goldbach_lower_outer_log (B N : ℝ) (hN : 1<N) :
    Real.log (goldbachLowerOuterLevel B N)=
      Real.log N-Real.log 24-B*Real.log (Real.log N)-(Real.log (Real.log N))^3 := by
  have hlog := Real.log_pos hN
  have hp := Real.rpow_pos_of_pos hlog B
  unfold goldbachLowerOuterLevel goldbachLowerSieveLevel
  rw [Real.log_div (div_ne_zero (by linarith) (mul_ne_zero (by norm_num) hp.ne'))
    (Real.exp_ne_zero _),Real.log_exp,
    Real.log_div (by linarith) (mul_ne_zero (by norm_num) hp.ne'),
    Real.log_mul (by norm_num) hp.ne',Real.log_rpow hlog]
  ring

theorem goldbach_lower_outer_log_ratio (B : ℝ) :
    Tendsto (fun N : ℝ=>Real.log (goldbachLowerOuterLevel B N)/Real.log N)
      atTop (nhds 1) := by
  have h₁ : Tendsto (fun N : ℝ=>Real.log (Real.log N)/Real.log N) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Real.tendsto_log_atTop
  have h₃ : Tendsto (fun N : ℝ=>(Real.log (Real.log N))^3/Real.log N) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp Real.tendsto_log_atTop
  have hc : Tendsto (fun N : ℝ=>Real.log 24/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hconst : Tendsto (fun _ : ℝ=>(1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := ((hconst.sub hc).sub (h₁.const_mul B)).sub h₃
  have hh' : Tendsto (fun N : ℝ=>1-Real.log 24/Real.log N-
      B*(Real.log (Real.log N)/Real.log N)-(Real.log (Real.log N))^3/Real.log N)
      atTop (nhds 1) := by simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  rw [goldbach_lower_outer_log B N hN]
  field_simp [(Real.log_pos hN).ne']

theorem goldbach_lower_sieve_parameter_tendsto (B : ℝ) :
    Tendsto (fun N : ℝ=>Real.log (goldbachLowerOuterLevel B N)/
      Real.log (goldbachLowerSiftingLimit N)) atTop (nhds ((9:ℝ)/8)) := by
  have h := (goldbach_lower_outer_log_ratio B).div_const ((8:ℝ)/9)
  apply (show Tendsto (fun N : ℝ=>(Real.log (goldbachLowerOuterLevel B N)/Real.log N)/((8:ℝ)/9))
    atTop (nhds ((9:ℝ)/8)) by convert h using 1; norm_num).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  rw [goldbachLowerSiftingLimit,Real.log_rpow (by linarith : 0<N)]
  ring

theorem goldbach_lower_sieve_levels_eventually (B C : ℝ) :
    ∀ᶠ N : ℝ in atTop,1<N ∧
      (Real.log N)^C+1≤goldbachLowerSiftingLimit N ∧
      goldbachLowerSiftingLimit N≤goldbachLowerOuterLevel B N ∧
      goldbachLowerOuterLevel B N≤N^(2:ℝ) := by
  have hl := (goldbach_lower_outer_log_ratio B).eventually (lt_mem_nhds (by norm_num : (8:ℝ)/9<1))
  have hu := (goldbach_lower_outer_log_ratio B).eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  filter_upwards [eventually_gt_atTop (1:ℝ),hl,hu,
    eventually_two_rpow_budget (K:=1) (L:=1) (a:=(4:ℝ)/9) (d:=0) (b:=(8:ℝ)/9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_log_rpow_le_rpow C (by norm_num : (0:ℝ)<4/9)] with N hN hl hu hp hlog
  have hNp : 0<N := by linarith
  have hln : 0<Real.log N := Real.log_pos hN
  have hD := goldbach_lower_outer_level_pos B N hN
  refine ⟨hN,?_,?_,?_⟩
  · dsimp [goldbachLowerSiftingLimit]
    have hp' : N^((4:ℝ)/9)+1≤N^((8:ℝ)/9) := by
      simpa only [one_mul,Real.rpow_zero] using hp
    linarith only [hlog,hp']
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hNp _) hD).mp
    rw [Real.log_rpow hNp]
    exact ((lt_div_iff₀ hln).mp hl).le
  · apply (Real.log_le_log_iff hD (Real.rpow_pos_of_pos hNp _)).mp
    rw [Real.log_rpow hNp]
    exact ((div_lt_iff₀ hln).mp hu).le

theorem goldbach_lower_product_level (B N : ℝ) :
    Real.exp ((Real.log (Real.log N))^3)*goldbachLowerOuterLevel B N=
      goldbachLowerSieveLevel B N := by
  unfold goldbachLowerOuterLevel
  exact mul_div_cancel₀ _ (Real.exp_ne_zero _)

end PrimeSquares
