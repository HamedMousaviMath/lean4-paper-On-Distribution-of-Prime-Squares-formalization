import PrimeSquares.IWOptimizedScaleCost

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwOptimizedDLogCoefficient (C : ℝ) : ℝ :=
  Real.log (Real.exp 1+1+iwOptimizedScaleCoefficient C)+784
noncomputable def iwOptimizedCostConstant (C : ℝ) : ℝ := 4*iwOptimizedDLogCoefficient C
noncomputable def iwOptimizedCostExponent (C : ℝ) : ℝ := 24*(1+iwMultiplierLogCoefficient C)

theorem iwOptimizedCostConstants_positive {C : ℝ} (hC : 2 ≤ C) :
    1 ≤ iwOptimizedDLogCoefficient C ∧ 1 ≤ iwOptimizedCostConstant C ∧
      1 ≤ iwOptimizedCostExponent C := by
  have hS := iwOptimizedScaleCoefficient_one_le hC
  have hA := iwMultiplierLogCoefficient_one_le hC
  have hl : 0 ≤ Real.log (Real.exp 1+1+iwOptimizedScaleCoefficient C) :=
    Real.log_nonneg (by linarith [Real.exp_pos (1 : ℝ)])
  unfold iwOptimizedDLogCoefficient iwOptimizedCostConstant iwOptimizedCostExponent
  dsimp [iwOptimizedDLogCoefficient]
  constructor
  · linarith
  constructor <;> linarith

theorem iwRestrictedMaximal_log_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    Real.log (Real.exp 1+(iwRestrictedCutoff v : ℝ)+(iwRestrictedOrder v : ℝ)*
      Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v))) ≤
        iwOptimizedDLogCoefficient C*v := by
  let A := Real.exp 1+1+iwOptimizedScaleCoefficient C
  let X := Real.exp 1+(iwRestrictedCutoff v : ℝ)+(iwRestrictedOrder v : ℝ)*
    Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v))
  have hS := iwOptimizedScaleCoefficient_one_le hC
  have hA : 1 ≤ A := by dsimp [A]; linarith [Real.exp_pos (1 : ℝ)]
  have hv0 : 0 ≤ v := by linarith
  have hE : 1 ≤ Real.exp (784*v) := Real.one_le_exp (by positivity)
  have hQp : (0 : ℝ) < iwRestrictedCutoff v := by unfold iwRestrictedCutoff; positivity
  have hQ : (iwRestrictedCutoff v : ℝ) ≤ Real.exp (784*v) := by
    calc
      _ = Real.exp (Real.log (iwRestrictedCutoff v : ℝ)) := (Real.exp_log hQp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [(iwRestrictedCutoff_bounds hv).2.2])
  have hcore := (nearOneCore_basic_bounds hv).2
  have hstart := iwRestrictedStartExpression_exp_bound hC hv
  have hstart' : iwRestrictedStartExpression C v ≤ iwOptimizedScaleCoefficient C*Real.exp (784*v) :=
    hstart.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith))
  have hterm : (iwRestrictedOrder v : ℝ)*Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v)) ≤
      iwOptimizedScaleCoefficient C*Real.exp (784*v) := by
    unfold iwRestrictedStartExpression at hstart'
    nlinarith [sq_nonneg (Real.log (iwRestrictedCutoff v : ℝ))]
  have he : Real.exp 1 ≤ Real.exp 1*Real.exp (784*v) :=
    le_mul_of_one_le_right (Real.exp_pos _).le hE
  have hX : X ≤ A*Real.exp (784*v) := by dsimp [X, A]; nlinarith
  have hX0 : 0 < X := by
    have hl := Real.log_nonneg (iwDenominatorBound_one_le hC (iwBalancedRank v) (iwRestrictedCutoff v))
    dsimp [X]
    positivity
  have h := Real.log_le_log hX0 hX
  rw [Real.log_mul (by linarith : A ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at h
  have hlogA := Real.log_nonneg hA
  have hm := mul_nonneg hlogA (show 0 ≤ v-1 by linarith)
  change Real.log X ≤ _
  unfold iwOptimizedDLogCoefficient
  dsimp [A] at h hm
  nlinarith

theorem iwRestrictedMaximal_exp_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    iwMaximalCost C (iwRestrictedOrder v) (iwBalancedRank v) (iwRestrictedCutoff v) ≤
      iwOptimizedCostConstant C*Real.exp (iwOptimizedCostExponent C*nearOneCore v) := by
  let L := Real.log (Real.exp 1+v)
  let k := (iwBalancedRank v : ℝ)
  let B := k*L+v/k
  let A := iwMultiplierLogCoefficient C
  have hL : 1 ≤ L := (nearOne_innerLog_bounds hv).1
  have hk : 4 ≤ k := by dsimp [k]; exact_mod_cast (iwRestrictedRank_bounds hv).1
  have hB : B ≤ 12*nearOneCore v := iwBalancedRank_optimization hv
  have hkL : k*L ≤ B := le_add_of_nonneg_right (by positivity)
  have hLB : L ≤ B := by
    have h := mul_nonneg (show 0 ≤ k-1 by linarith) (show 0 ≤ L by linarith)
    linarith
  have hA : 1 ≤ A := iwMultiplierLogCoefficient_one_le hC
  have hlog := iwRestrictedMaximal_log_bound hC hv
  have hr := (iwRestrictedOrder_bounds hv).2.2.2
  have hCrk := iwRestrictedMultiplier_exp_bound hC hv
  have hCrk0 : 0 ≤ iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v) := by
    unfold iwMultiplierConstant
    exact Real.rpow_nonneg (by
      have hlogk := Real.log_nonneg (show (1 : ℝ) ≤ 2+iwBalancedRank v by have hn := (Nat.cast_nonneg (iwBalancedRank v) : (0 : ℝ) ≤ iwBalancedRank v); linarith)
      positivity) _
  have hsquare := pow_le_pow_left₀ hCrk0 hCrk 2
  have hDl := iwOptimizedCostConstants_positive hC
  have hD0 : 0 ≤ iwOptimizedDLogCoefficient C := by linarith [hDl.1]
  have hv0 : 0 ≤ v := by linarith
  have hlog0 : 0 ≤ Real.log (Real.exp 1+(iwRestrictedCutoff v : ℝ)+(iwRestrictedOrder v : ℝ)*
      Real.log (iwDenominatorBound C (iwBalancedRank v) (iwRestrictedCutoff v))) := by
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hl := Real.log_nonneg (iwDenominatorBound_one_le hC (iwBalancedRank v) (iwRestrictedCutoff v))
    have hm := mul_nonneg (Nat.cast_nonneg (iwRestrictedOrder v) : (0 : ℝ) ≤ iwRestrictedOrder v) hl
    have hq := (Nat.cast_nonneg (iwRestrictedCutoff v) : (0 : ℝ) ≤ iwRestrictedCutoff v)
    linarith
  have hvE : v ≤ Real.exp L := by
    dsimp [L]
    rw [Real.exp_log (by positivity : 0 < Real.exp 1+v)]
    linarith [Real.exp_pos (1 : ℝ)]
  have hv2 : v^2 ≤ Real.exp (2*L) := by
    calc
      _ ≤ (Real.exp L)^2 := pow_le_pow_left₀ hv0 hvE 2
      _ = _ := by rw [pow_two, ←Real.exp_add]; congr 1; ring
  have hexp : 2*L+2*A*k*L ≤ iwOptimizedCostExponent C*nearOneCore v := by
    have h1 := mul_le_mul_of_nonneg_left hLB (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left hkL (show 0 ≤ 2*A by linarith)
    have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2+2*A by linarith)
    unfold iwOptimizedCostExponent
    dsimp [A] at *
    nlinarith
  calc
    _ ≤ (4*v)*(Real.exp (A*k*L))^2*(iwOptimizedDLogCoefficient C*v) :=
      mul_le_mul (mul_le_mul hr hsquare (sq_nonneg _) (by positivity)) hlog hlog0 (by positivity)
    _ = iwOptimizedCostConstant C*v^2*Real.exp (2*A*k*L) := by
      unfold iwOptimizedCostConstant
      rw [show (Real.exp (A*k*L))^2 = Real.exp (2*A*k*L) by
        rw [pow_two, ←Real.exp_add]; congr 1; ring]
      ring
    _ ≤ iwOptimizedCostConstant C*Real.exp (2*L)*Real.exp (2*A*k*L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 (by unfold iwOptimizedCostConstant; positivity)) (Real.exp_pos _).le
    _ = iwOptimizedCostConstant C*Real.exp (2*L+2*A*k*L) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by unfold iwOptimizedCostConstant; positivity)

end PrimeSquares
