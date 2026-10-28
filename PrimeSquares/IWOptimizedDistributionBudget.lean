import PrimeSquares.IWOptimizedStartingIndex
import PrimeSquares.IWFullLowMaximum

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwRestrictedGaugeRate (C : ℝ) : ℝ := 384+2*iwOptimizedCostExponent C
noncomputable def iwRestrictedBudgetConstant (C Cstart K KH mass : ℝ) : ℝ :=
  mass*(2*Cstart*iwOptimizedScaleCoefficient C+2)+
    4*Real.exp 1*(1+2*K*iwOptimizedCostConstant C)^2+4*KH^2

theorem iwRestrictedLow_power_bound {C K v : ℝ} (hC : 2 ≤ C) (hK : 0 ≤ K) (hv : 1 ≤ v) :
    (2*K*iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v))^
      (iwNearOneExponent (iwRestrictedOrder v)) ≤
    (1+2*K*iwOptimizedCostConstant C)^2*
      Real.exp (2*iwOptimizedCostExponent C*nearOneCore v) := by
  let A := 1+2*K*iwOptimizedCostConstant C
  let X := iwOptimizedCostExponent C*nearOneCore v
  let p := iwNearOneExponent (iwRestrictedOrder v)
  have hr := (iwRestrictedOrder_bounds hv).1
  have hp := iwNearOneExponent_bounds hr
  have hc := iwOptimizedCostConstants_positive hC
  have hCore := (nearOneCore_basic_bounds hv).1
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [hc.2.1]
  have hX : 0 ≤ X := mul_nonneg (by linarith [hc.2.2]) (by linarith)
  have hD := iwRestrictedMaximal_exp_bound hC hv
  have hD0 : 0 ≤ iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v) :=
    (by positivity : 0 ≤ (iwRestrictedOrder v : ℝ)*(iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v))^2).trans
      (iwMaximalCost_lower_bounds hC hr _ _).1
  have hbase : 2*K*iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v) ≤ A*Real.exp X := by
    have h := mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*K by positivity)
    dsimp [A, X]
    nlinarith [Real.exp_pos (iwOptimizedCostExponent C*nearOneCore v)]
  have hAp : A^p ≤ A^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hA (show p ≤ 2 by dsimp [p]; linarith [hp.2])
  have hXp : (Real.exp X)^p ≤ Real.exp (2*X) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos X), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (show p ≤ 2 by dsimp [p]; linarith [hp.2]) hX
    nlinarith
  calc
    _ ≤ (A*Real.exp X)^p := Real.rpow_le_rpow (by positivity) hbase (by dsimp [p]; linarith [hp.1])
    _ = A^p*(Real.exp X)^p := Real.mul_rpow (by linarith) (Real.exp_pos _).le
    _ ≤ A^2*Real.exp (2*X) := mul_le_mul hAp hXp (by positivity) (sq_nonneg A)
    _ = _ := by dsimp [A, X]; congr 2; ring

theorem iwRestrictedBudget_constants {C Cstart K KH mass : ℝ}
    (hC : 2 ≤ C) (hstart : 0 < Cstart) (hK : 0 ≤ K) (hm : 0 ≤ mass) :
    0 ≤ iwRestrictedGaugeRate C ∧ 0 < iwRestrictedBudgetConstant C Cstart K KH mass := by
  have hc := iwOptimizedCostConstants_positive hC
  have hs := iwOptimizedScaleCoefficient_one_le hC
  have hA : 1 ≤ 1+2*K*iwOptimizedCostConstant C := by nlinarith [hc.2.1]
  unfold iwRestrictedGaugeRate iwRestrictedBudgetConstant
  constructor
  · linarith [hc.2.2]
  · have hfirst : 0 ≤ mass*(2*Cstart*iwOptimizedScaleCoefficient C+2) := by positivity
    have hsecond : 0 < 4*Real.exp 1*(1+2*K*iwOptimizedCostConstant C)^2 := by positivity
    nlinarith [sq_nonneg KH]

theorem iwRestrictedDistribution_budget {C Cstart K KH mass t : ℝ}
    (hC : 2 ≤ C) (hstart : 0 < Cstart) (hK : 0 ≤ K) (hm : 0 ≤ mass) (ht : 1 ≤ t) :
    t*(iwRestrictedStartingIndex C Cstart (nearOneLog t) : ℝ)*mass+
      (2*t)^(iwNearOneExponent (iwRestrictedOrder (nearOneLog t)))*
        ((2*K*iwMaximalCost C (iwRestrictedOrder (nearOneLog t)) (iwBalancedRank (nearOneLog t)) (iwRestrictedCutoff (nearOneLog t)))^
          (iwNearOneExponent (iwRestrictedOrder (nearOneLog t))))+
      4*t^2*(KH^2*(iwRestrictedCutoff (nearOneLog t) : ℝ)^(-(1/2 : ℝ))) ≤
    iwRestrictedBudgetConstant C Cstart K KH mass*t*
      Real.exp (iwRestrictedGaugeRate C*nearOneCore (nearOneLog t)) := by
  let v := nearOneLog t
  let E := Real.exp (iwRestrictedGaugeRate C*nearOneCore v)
  let A := 1+2*K*iwOptimizedCostConstant C
  have hv : 1 ≤ v := nearOneLog_one_le t
  have hvCore : 0 ≤ nearOneCore v := by linarith [(nearOneCore_basic_bounds hv).1]
  have hc := iwOptimizedCostConstants_positive hC
  have hrate := (iwRestrictedBudget_constants (KH:=KH) hC hstart hK hm).1
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hrate hvCore)
  have hsmallExp : Real.exp (384*nearOneCore v) ≤ E :=
    Real.exp_le_exp.mpr (by dsimp [iwRestrictedGaugeRate]; nlinarith [hc.2.2])
  have hlowExp : Real.exp (2*iwOptimizedCostExponent C*nearOneCore v) ≤ E :=
    Real.exp_le_exp.mpr (by dsimp [iwRestrictedGaugeRate]; nlinarith)
  have hJ := iwRestrictedStartingIndex_exp_bound hC hstart hv
  have hs := iwOptimizedScaleCoefficient_one_le hC
  have hJ' : (iwRestrictedStartingIndex C Cstart v : ℝ) ≤
      (2*Cstart*iwOptimizedScaleCoefficient C+2)*E :=
    hJ.trans (mul_le_mul_of_nonneg_left hsmallExp (by positivity))
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ' (show 0 ≤ t by linarith)) hm
  have hLow := iwRestrictedLow_power_bound hC hK hv
  have hlow' := hLow.trans (mul_le_mul_of_nonneg_left hlowExp (sq_nonneg A))
  have hD0 : 0 ≤ iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v) :=
    (by positivity : 0 ≤ (iwRestrictedOrder v : ℝ)*(iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v))^2).trans
      (iwMaximalCost_lower_bounds hC (iwRestrictedOrder_bounds hv).1 _ _).1
  have hbase0 : 0 ≤ 2*K*iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v) := by positivity
  have hsecond := mul_le_mul (iwRestricted_two_t_power ht) hlow' (Real.rpow_nonneg hbase0 _) (by positivity : 0 ≤ 4*Real.exp 1*t)
  have hhigh := iwRestricted_high_cost ht
  have hthird : 4*t^2*(KH^2*(iwRestrictedCutoff v : ℝ)^(-(1/2 : ℝ))) ≤ 4*KH^2*t*E := by
    have h := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ 4*KH^2*t by positivity)
    have h' := le_mul_of_one_le_right (show 0 ≤ 4*KH^2*t by positivity) hE
    dsimp [v] at *
    nlinarith
  change _ ≤ iwRestrictedBudgetConstant C Cstart K KH mass*t*E
  unfold iwRestrictedBudgetConstant
  dsimp [v, A] at *
  nlinarith

end PrimeSquares
