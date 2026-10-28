import PrimeSquares.IWOptimizedMultiplierCost

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwRestrictedStartExpression (C v : ℝ) : ℝ :=
  (Real.log (iwRestrictedCutoff v : ℝ))^2+
    (iwRestrictedOrder v : ℝ)*Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v))

noncomputable def iwOptimizedScaleCoefficient (C : ℝ) : ℝ := 256+196*Real.log C

theorem iwRestrictedStartExpression_nonneg {C : ℝ} (hC : 2 ≤ C) (v : ℝ) :
    0 ≤ iwRestrictedStartExpression C v := by
  unfold iwRestrictedStartExpression
  exact add_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (iwDenominatorBound_one_le hC _ _)))

theorem iwOptimizedScaleCoefficient_one_le {C : ℝ} (hC : 2 ≤ C) :
    1 ≤ iwOptimizedScaleCoefficient C := by
  have h := Real.log_nonneg (show 1 ≤ C by linarith)
  unfold iwOptimizedScaleCoefficient
  linarith

theorem iwRestrictedDenominator_log_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v)) ≤
      (iwBalancedRank v : ℝ)^2*Real.exp (32*v/(iwBalancedRank v : ℝ))*Real.log C := by
  let k := (iwBalancedRank v : ℝ)
  have hk : 4 ≤ k := by dsimp [k]; exact_mod_cast (iwRestrictedRank_bounds hv).1
  have hk0 : 0 < k := by linarith
  have hd : 0 < k-1/2 := by linarith
  have hQ : (0 : ℝ) < iwRestrictedCutoff v := by unfold iwRestrictedCutoff; positivity
  have hlogC := Real.log_nonneg (show 1 ≤ C by linarith)
  have hfrac : Real.log (iwRestrictedCutoff v : ℝ)/(k-1/2) ≤ 32*v/k := by
    apply (div_le_iff₀ hd).mpr
    have hdiv : 32*v/k*(k-1/2) ≥ 16*v := by
      rw [show 32*v/k*(k-1/2) = 32*v*(k-1/2)/k by ring]
      apply (le_div_iff₀ hk0).mpr
      nlinarith
    exact (iwRestrictedCutoff_bounds hv).2.2.trans hdiv
  have hp : (iwRestrictedCutoff v : ℝ)^(1/(k-1/2)) ≤ Real.exp (32*v/k) := by
    rw [Real.rpow_def_of_pos hQ]
    apply Real.exp_le_exp.mpr
    simpa only [mul_one_div] using hfrac
  rw [iwDenominatorBound_log (by linarith : 0 < C)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg k)) hlogC

theorem iwRestrictedStartExpression_polynomial_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    iwRestrictedStartExpression C v ≤
      iwOptimizedScaleCoefficient C*v^3*Real.exp (32*v/(iwBalancedRank v : ℝ)) := by
  let r := (iwRestrictedOrder v : ℝ)
  let k := (iwBalancedRank v : ℝ)
  let U := Real.exp (32*v/k)
  have hr : r ≤ 4*v := (iwRestrictedOrder_bounds hv).2.2.2
  have hk : k ≤ 7*v := (iwRestrictedRank_bounds hv).2.2
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := by linarith
  have hU : 1 ≤ U := Real.one_le_exp (by positivity)
  have hlogC := Real.log_nonneg (show 1 ≤ C by linarith)
  have hq := iwRestrictedCutoff_bounds hv
  have hq0 : 0 ≤ Real.log (iwRestrictedCutoff v : ℝ) := by linarith [hq.2.1]
  have hsq : (Real.log (iwRestrictedCutoff v : ℝ))^2 ≤ 256*v^2 := by nlinarith [hq.2.2]
  have hk2 : k^2 ≤ 49*v^2 := by nlinarith
  have hrk : r*k^2 ≤ 196*v^3 := by
    calc
      _ ≤ (4*v)*(49*v^2) := mul_le_mul hr hk2 (sq_nonneg k) (by positivity)
      _ = _ := by ring
  have hlogB := iwRestrictedDenominator_log_bound hC hv
  have hterm : r*Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v)) ≤
      196*v^3*U*Real.log C := by
    calc
      _ ≤ r*(k^2*U*Real.log C) := mul_le_mul_of_nonneg_left hlogB hr0
      _ = (r*k^2)*U*Real.log C := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrk (by positivity)) hlogC
  have hv23 : v^2 ≤ v^3 := by nlinarith [sq_nonneg v]
  have hv3 : v^3 ≤ v^3*U := le_mul_of_one_le_right (by positivity) hU
  have hsq' : (Real.log (iwRestrictedCutoff v : ℝ))^2 ≤ 256*v^3*U := by nlinarith
  change (Real.log (iwRestrictedCutoff v : ℝ))^2+r*Real.log _ ≤ _
  unfold iwOptimizedScaleCoefficient
  nlinarith

theorem iwRestrictedStartExpression_exp_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    iwRestrictedStartExpression C v ≤ iwOptimizedScaleCoefficient C*Real.exp (384*nearOneCore v) := by
  let L := Real.log (Real.exp 1+v)
  let k := (iwBalancedRank v : ℝ)
  have hL : 1 ≤ L := (nearOne_innerLog_bounds hv).1
  have hk : 4 ≤ k := by dsimp [k]; exact_mod_cast (iwRestrictedRank_bounds hv).1
  have hv0 : 0 ≤ v := by linarith
  have hvE : v ≤ Real.exp L := by
    dsimp [L]
    rw [Real.exp_log (by positivity : 0 < Real.exp 1+v)]
    linarith [Real.exp_pos (1 : ℝ)]
  have hv3 : v^3 ≤ Real.exp (3*L) := by
    calc
      _ ≤ (Real.exp L)^3 := pow_le_pow_left₀ hv0 hvE 3
      _ = _ := by rw [←Real.exp_nat_mul]; norm_num
  have hcoef : 0 ≤ iwOptimizedScaleCoefficient C := by linarith [iwOptimizedScaleCoefficient_one_le hC]
  have hbal := iwBalancedRank_optimization hv
  change k*L+v/k ≤ 12*nearOneCore v at hbal
  have hexp : 3*L+32*v/k ≤ 384*nearOneCore v := by
    have h := mul_nonneg (show 0 ≤ 32*k-3 by linarith) (show 0 ≤ L by linarith)
    simp only [div_eq_mul_inv] at hbal ⊢
    nlinarith
  calc
    _ ≤ iwOptimizedScaleCoefficient C*v^3*Real.exp (32*v/k) := iwRestrictedStartExpression_polynomial_bound hC hv
    _ ≤ iwOptimizedScaleCoefficient C*Real.exp (3*L)*Real.exp (32*v/k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv3 hcoef) (Real.exp_pos _).le
    _ = iwOptimizedScaleCoefficient C*Real.exp (3*L+32*v/k) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hcoef

end PrimeSquares
