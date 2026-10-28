import PrimeSquares.IWRestrictedParameters

set_option autoImplicit false
namespace PrimeSquares

theorem nearOneCore_basic_bounds {v : ℝ} (hv : 1 ≤ v) :
    1 ≤ nearOneCore v ∧ nearOneCore v ≤ 2*v := by
  obtain ⟨hL, hL2⟩ := nearOne_innerLog_bounds hv
  have hv0 : 0 ≤ v := by linarith
  have hL0 : 0 ≤ Real.log (Real.exp 1+v) := by linarith
  have hs := Real.sq_sqrt (mul_nonneg hv0 hL0)
  have hs0 := Real.sqrt_nonneg (v*Real.log (Real.exp 1+v))
  have hlo := mul_le_mul hv hL (by norm_num : (0 : ℝ) ≤ 1) hv0
  have hhi := mul_le_mul_of_nonneg_left hL2 hv0
  unfold nearOneCore
  constructor <;> nlinarith

noncomputable def iwMultiplierLogCoefficient (C : ℝ) : ℝ := C*(Real.log C+20)

theorem iwMultiplierLogCoefficient_one_le {C : ℝ} (hC : 2 ≤ C) :
    1 ≤ iwMultiplierLogCoefficient C := by
  have hl := Real.log_nonneg (by linarith : 1 ≤ C)
  unfold iwMultiplierLogCoefficient
  nlinarith

theorem iwRestrictedMultiplier_log_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    Real.log (iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v)) ≤
      iwMultiplierLogCoefficient C*(iwBalancedRank v : ℝ)*Real.log (Real.exp 1+v) := by
  let r := iwRestrictedOrder v
  let k := iwBalancedRank v
  let L := Real.log (Real.exp 1+v)
  have hr := iwRestrictedOrder_bounds hv
  have hk := iwRestrictedRank_bounds hv
  have hvp : 0 < v := by linarith
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by have h := hr.1; omega)
  have hkp : (4 : ℝ) ≤ k := by exact_mod_cast hk.1
  have hL : 1 ≤ L := (nearOne_innerLog_bounds hv).1
  have hlogv : Real.log v ≤ L := Real.log_le_log hvp (by
    have h := Real.exp_pos (1 : ℝ)
    linarith)
  have hlogr : Real.log (r : ℝ) ≤ 4*L := by
    have h := Real.log_le_log hrp hr.2.2.2
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hvp.ne'] at h
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogkpos : 0 < Real.log (2+(k : ℝ)) := Real.log_pos (by linarith)
  have hlogk : Real.log (2+(k : ℝ)) ≤ 9*L := by
    have harg : 2+(k : ℝ) ≤ 9*v := by dsimp [k]; linarith [hk.2.2]
    have h := Real.log_le_log (by linarith : (0 : ℝ) < 2+(k : ℝ)) harg
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) hvp.ne'] at h
    have h9 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  have hloglog : Real.log (Real.log (2+(k : ℝ))) ≤ 9*L := by
    have h := Real.log_le_sub_one_of_pos hlogkpos
    linarith
  have hbase : Real.log (C*(r : ℝ)*Real.log (2+(k : ℝ))) ≤ (Real.log C+20)*L := by
    rw [Real.log_mul (mul_pos hCpos hrp).ne' hlogkpos.ne', Real.log_mul hCpos.ne' hrp.ne']
    have hm := mul_nonneg hlogC (show 0 ≤ L-1 by linarith)
    nlinarith
  change Real.log (iwMultiplierConstant C r k) ≤ _
  rw [iwMultiplierConstant, Real.log_rpow (mul_pos (mul_pos hCpos hrp) hlogkpos)]
  calc
    _ ≤ (C*(k : ℝ))*((Real.log C+20)*L) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by unfold iwMultiplierLogCoefficient; dsimp [k, L]; ring

theorem iwRestrictedMultiplier_exp_bound {C v : ℝ} (hC : 2 ≤ C) (hv : 1 ≤ v) :
    iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v) ≤
      Real.exp (iwMultiplierLogCoefficient C*(iwBalancedRank v : ℝ)*Real.log (Real.exp 1+v)) := by
  have hr := (iwRestrictedOrder_bounds hv).1
  have hk := (iwRestrictedRank_bounds hv).1
  have hrR : (0 : ℝ) < iwRestrictedOrder v := by exact_mod_cast (show 0 < iwRestrictedOrder v by omega)
  have hkR : (4 : ℝ) ≤ iwBalancedRank v := by exact_mod_cast hk
  have hlog : 0 < Real.log (2+(iwBalancedRank v : ℝ)) := Real.log_pos (by linarith)
  have hp : 0 < iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v) := by
    unfold iwMultiplierConstant
    apply Real.rpow_pos_of_pos
    exact mul_pos (mul_pos (by linarith : 0 < C) hrR) hlog
  calc
    _ = Real.exp (Real.log (iwMultiplierConstant C (iwRestrictedOrder v) (iwBalancedRank v))) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (iwRestrictedMultiplier_log_bound hC hv)

end PrimeSquares
