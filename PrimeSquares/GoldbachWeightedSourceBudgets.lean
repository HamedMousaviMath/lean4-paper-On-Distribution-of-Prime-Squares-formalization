import PrimeSquares.GoldbachWeightedErrorBounds

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_weighted_source_budgets (A C K₁ Ks K M ε : ℝ) (hC : 0<C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,2≤N ∧ 2≤Real.log N ∧ 3≤(Real.log N)^C ∧
      (Real.log N)^C<(N:ℝ)^(2/9:ℝ) ∧ Real.log ((Real.log N)^C)≤Real.log N ∧
      K₁/Real.log ((Real.log N)^C)≤ε ∧ 8*Ks/Real.log N≤ε ∧
      ((768*M/(Real.log 2)^3)/(Real.log N)^3+(48*M*K)/(Real.log N)^2)≤ε ∧
      (64:ℝ)≤N ∧ (N:ℝ)≤(N:ℝ)^2*(Real.log N)^(-A) ∧
      (N:ℝ)≤(N:ℝ)^2*(Real.log N)^(-(A+14)) := by
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLog := Real.tendsto_log_atTop.comp hNat
  have hR : Tendsto (fun N : ℕ=>(Real.log N)^C) atTop atTop := (tendsto_rpow_atTop hC).comp hLog
  have hq := Real.tendsto_log_atTop.comp hR
  have hK : Tendsto (fun N : ℕ=>K₁/Real.log ((Real.log N)^C)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hq
  have hs : Tendsto (fun N : ℕ=>8*Ks/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLog
  have herr := (goldbach_weighted_error_coefficient_limit M K).comp hLog
  have hRatio : Tendsto (fun L : ℝ=>C*Real.log L/L) atTop (nhds 0) := by
    simpa only [one_mul,add_zero,pow_one,mul_div_assoc,mul_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul C
  filter_upwards [hNat.eventually (goldbach_retained_height_eventually A),
    hNat.eventually (goldbach_retained_height_eventually (A+14)),
    hLog.eventually_ge_atTop 2,hR.eventually_ge_atTop 3,
    (hRatio.comp hLog).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2/9)),
    hK.eventually (gt_mem_nhds hε),hs.eventually (gt_mem_nhds hε),
    herr.eventually (gt_mem_nhds hε)] with N hheight hheightT hlog hR hratio hK hs herr
  dsimp only [Function.comp_apply] at hheight hheightT hlog hratio herr
  have hN : 2≤N := by exact_mod_cast (show (2:ℝ)≤N by linarith [hheight.1])
  have hN0 : (0:ℝ)<N := by linarith [hheight.1]
  have hlog0 : 0<Real.log (N:ℝ) := by linarith
  have hR0 : 0<(Real.log N)^C := by linarith
  have hlogR : Real.log ((Real.log N)^C)=C*Real.log (Real.log N) := Real.log_rpow hlog0 C
  have hratio' := (div_lt_iff₀ hlog0).mp hratio
  have hRN : (Real.log N)^C<(N:ℝ)^(2/9:ℝ) := by
    apply (Real.log_lt_log_iff hR0 (Real.rpow_pos_of_pos hN0 _)).mp
    rw [hlogR,Real.log_rpow hN0]
    exact hratio'
  refine ⟨hN,hlog,hR,hRN,?_,hK.le,hs.le,herr.le,hheight.1,hheight.2,hheightT.2⟩
  rw [hlogR]
  linarith

end PrimeSquares
