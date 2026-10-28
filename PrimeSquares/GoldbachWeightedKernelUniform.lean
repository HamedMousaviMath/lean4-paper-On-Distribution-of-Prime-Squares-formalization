import PrimeSquares.GoldbachWeightedKernelEffective
import PrimeSquares.GoldbachWeightedCutoffBudgets

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_weighted_choose_mean_parameter (K δ W η : ℝ) (hK : 0≤K)
    (hδ : 0<δ) (hW : 0≤W) (hη : 0<η) :
    ∃ ε : ℝ,0<ε ∧ ε≤1/2 ∧ (goldbachHalfMeanConstant+K*ε^δ)*W<goldbachHalfMeanConstant*W+η/2 := by
  let b := η/(4*(K+1)*(W+1))
  let ε := min (1/2:ℝ) (b^(δ⁻¹))
  have hb : 0<b := by dsimp only [b];positivity
  have hε : 0<ε := lt_min (by norm_num) (Real.rpow_pos_of_pos hb _)
  have hεB : ε≤1/2 := min_le_left _ _
  have hp : ε^δ≤b := by
    have hh := Real.rpow_le_rpow hε.le (min_le_right (1/2:ℝ) (b^(δ⁻¹))) hδ.le
    rwa [Real.rpow_inv_rpow hb.le hδ.ne'] at hh
  have hKW : K*W≤(K+1)*(W+1) := by nlinarith only [hK,hW]
  have hh := mul_le_mul hp hKW (mul_nonneg hK hW) hb.le
  have he : b*((K+1)*(W+1))=η/4 := by dsimp only [b];field_simp
  rw [he] at hh
  refine ⟨ε,hε,hεB,?_⟩
  nlinarith only [hh,hη]

theorem goldbach_weighted_fixed_kernel_uniform (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ K₂ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) (C η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop,∀ n : ℤ,
      goldbachWeightedFixedKernel N ((N:ℝ)^(8/9:ℝ)) ((Real.log N)^C) n≤
        (goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*
        (goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
          (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N)) := by
  obtain ⟨K,δ,D,A,P,hK,hδ,hD,hA,hP,hbound⟩ := goldbach_weighted_kernel_effective
    hT K₀ K₁ K₂ hK₀ hK₁ hK₂ hM hV hI
  obtain ⟨ε,hε,hεB,hεsmall⟩ := goldbach_weighted_choose_mean_parameter K δ
    (goldbachWeightedW (9/8)) η hK.le hδ goldbach_weighted_W_nonneg hη
  have hLimit := goldbach_weighted_kernel_coefficient_limit C P A K δ K₀ K₁ ε hC hP.le hA.le
  have hcoef := hLimit.eventually (gt_mem_nhds
    (show (goldbachHalfMeanConstant+K*ε^δ)*goldbachWeightedW (9/8)<
      goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η by linarith))
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLog := Real.tendsto_log_atTop.comp hNat
  filter_upwards [hLog.eventually (goldbach_weighted_cutoffs_eventually C D K₀ ε hC hD hK₀ hε),
    hLog.eventually hcoef,eventually_ge_atTop 2] with N hcut hcoef hN
  dsimp only [Function.comp_apply] at hcut hcoef
  obtain ⟨hL,hKL,hR,ha,ha16,haU,hRD,hInv,hRa,hbudget,hexp⟩ := hcut
  intro n
  have hh := hbound C ε hC hε hεB N hN hL hKL hR ha ha16 haU hRD hInv hRa hbudget hexp n
  have hlog : 0<Real.log (N:ℝ) := by linarith
  have hlogR : Real.log ((Real.log N)^C)=C*Real.log (Real.log N) := Real.log_rpow hlog C
  have hR0 : 0≤(Real.log N)^C := Real.rpow_nonneg hlog.le C
  have hratio : 0≤goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n :=
    div_nonneg (goldbach_weighted_C_positive _ hR0 n).le (goldbach_weighted_B_positive _ hR0 n).le
  have hfac : 0≤(goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
      (Real.sqrt (C*Real.log (Real.log N))*Real.log N*Real.sqrt (Real.log N)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hcoef.le hfac
  apply (hh.trans hm).trans_eq
  rw [hlogR]
  ring

end PrimeSquares
