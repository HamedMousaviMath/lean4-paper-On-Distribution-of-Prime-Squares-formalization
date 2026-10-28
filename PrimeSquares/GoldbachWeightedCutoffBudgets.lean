import PrimeSquares.GoldbachWeightedScaleLimits

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_weighted_cutoffs_eventually (C D K ε : ℝ) (hC : 0<C)
    (_hD : 1<D) (_hK : 0≤K) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,9≤L ∧ K≤L ∧ Real.exp 2≤L^C ∧
      2≤Real.exp (Real.sqrt L) ∧ Real.exp 16<Real.exp (Real.sqrt L) ∧
      Real.exp (Real.sqrt L)≤Real.exp ((2*L)/9)/2 ∧
      (L^C)^D≤Real.exp (Real.sqrt L) ∧
      1/Real.sqrt (Real.log (Real.exp (Real.sqrt L)))<ε ∧
      L^C≤(Real.exp (Real.sqrt L))^ε ∧
      6*Real.log (L^C)+10*K≤ε^2*Real.log (Real.exp (Real.sqrt L)) ∧
      L≤Real.exp ((8/9:ℝ)*L) := by
  have hLog : Tendsto (fun L : ℝ=>C*Real.log L) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hC
  have hRoot : Tendsto (fun L : ℝ=>Real.sqrt L) atTop atTop := Real.tendsto_sqrt_atTop
  have hRatio : Tendsto (fun L : ℝ=>(C*Real.log L)/Real.sqrt L) atTop (nhds 0) := by
    simpa only [pow_one,mul_div_assoc,mul_zero] using
      (goldbach_weighted_log_power_sqrt_limit 1).const_mul C
  have hDRatio : Tendsto (fun L : ℝ=>(D*(C*Real.log L))/Real.sqrt L) atTop (nhds 0) := by
    simpa only [mul_div_assoc,mul_zero] using hRatio.const_mul D
  have hConst : Tendsto (fun L : ℝ=>(10*K)/Real.sqrt L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hRoot
  have hBudget : Tendsto (fun L : ℝ=>(6*(C*Real.log L)+10*K)/Real.sqrt L) atTop (nhds 0) := by
    simpa only [add_div,mul_div_assoc,mul_zero,zero_add] using (hRatio.const_mul 6).add hConst
  have hInv : Tendsto (fun L : ℝ=>1/Real.sqrt (Real.sqrt L)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hRoot)
  filter_upwards [eventually_ge_atTop (100:ℝ),eventually_ge_atTop K,hLog.eventually_ge_atTop 2,
    hRoot.eventually_gt_atTop 16,
    hRatio.eventually (gt_mem_nhds hε),hDRatio.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hBudget.eventually (gt_mem_nhds (sq_pos_of_pos hε)),hInv.eventually (gt_mem_nhds hε)]
    with L hL hKL hlogRmin hroot hratio hdRatio hbudget hInv
  have hL0 : 0<L := by linarith
  have hs0 : 0<Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hR0 : 0<L^C := Real.rpow_pos_of_pos hL0 C
  have hlogR : Real.log (L^C)=C*Real.log L := Real.log_rpow hL0 C
  have hRbig : Real.exp 2≤L^C := by
    have hh := Real.exp_le_exp.mpr hlogRmin
    rwa [←Real.log_rpow hL0 C,Real.exp_log hR0] at hh
  have ha2 : 2≤Real.exp (Real.sqrt L) := by
    have hh := Real.add_one_le_exp (Real.sqrt L)
    linarith
  have haU : Real.exp (Real.sqrt L)≤Real.exp ((2*L)/9)/2 := by
    have hs : Real.sqrt L≤L/10 := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      have hh := mul_nonneg hL0.le (show 0≤L-100 by linarith)
      nlinarith only [hh]
    have hlog2 : Real.log 2≤1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have hh := Real.exp_le_exp.mpr (show Real.sqrt L+Real.log 2≤(2*L)/9 by linarith)
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
    exact (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith)
  have hDa : (L^C)^D≤Real.exp (Real.sqrt L) := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hR0 D) (Real.exp_pos _)).mp
    rw [Real.log_rpow hR0,hlogR,Real.log_exp]
    simpa only [one_mul] using ((div_lt_iff₀ hs0).mp hdRatio).le
  have hRa : L^C≤(Real.exp (Real.sqrt L))^ε := by
    apply (Real.log_le_log_iff hR0 (Real.rpow_pos_of_pos (Real.exp_pos _) ε)).mp
    rw [hlogR,Real.log_rpow (Real.exp_pos _),Real.log_exp]
    exact ((div_lt_iff₀ hs0).mp hratio).le
  have hB : 6*Real.log (L^C)+10*K≤ε^2*Real.log (Real.exp (Real.sqrt L)) := by
    rw [hlogR,Real.log_exp]
    exact ((div_lt_iff₀ hs0).mp hbudget).le
  have hExp : L≤Real.exp ((8/9:ℝ)*L) := by
    have hbound := Real.add_one_le_exp ((4/9:ℝ)*L)
    have hsq := mul_self_le_mul_self (by positivity : 0≤(4/9:ℝ)*L+1) hbound
    rw [show (8/9:ℝ)*L=(4/9:ℝ)*L+(4/9:ℝ)*L by ring,Real.exp_add]
    have hquad := mul_nonneg hL0.le (show 0≤L-100 by linarith)
    nlinarith only [hsq,hquad,hL]
  refine ⟨by linarith,hKL,hRbig,ha2,Real.exp_lt_exp.mpr (by linarith),haU,hDa,?_,hRa,hB,hExp⟩
  simpa only [Real.log_exp] using hInv

end PrimeSquares
