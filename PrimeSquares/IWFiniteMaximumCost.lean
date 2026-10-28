import PrimeSquares.IWShortScaleMaximum
import PrimeSquares.IWTransitionScale

set_option autoImplicit false
namespace PrimeSquares

theorem iw_short_scale_cost_bound {C : ℝ} (hC : 0≤ C) {r : ℕ} (hr : 2≤ r)
    (Z R : ℝ) (k J : ℕ) :
    iwShortScaleCost C Z R r k J≤
      (cutoffL1Constant+R*iwAnnularIncrementCost Z)*(r : ℝ)*iwMultiplierConstant C r k*
        Real.log (2+(J : ℝ)) := by
  have hmult := iwMultiplierConstant_nonneg hC r k
  have hcut := cutoffL1Constant_nonneg
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hlog : (1/2 : ℝ)≤ Real.log (2+(J : ℝ)) :=
    real_log_two_half_le.trans (Real.log_le_log (by norm_num : (0 : ℝ)<2)
      (by have hJ : (0 : ℝ)≤ J := Nat.cast_nonneg J;linarith))
  have hs : 1≤(r : ℝ)*Real.log (2+(J : ℝ)) := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hs (mul_nonneg hmult hcut)
  rw [mul_one] at hb
  unfold iwShortScaleCost
  calc
    _ ≤ (iwMultiplierConstant C r k*cutoffL1Constant)*((r : ℝ)*Real.log (2+(J : ℝ)))+
        (R*Real.log (2+(J : ℝ)))*(iwAnnularIncrementCost Z*(r : ℝ)*iwMultiplierConstant C r k) :=
      by linarith
    _ = _ := by ring

theorem iwMultiplierConstant_one_le {C : ℝ} (hC : 2≤ C) {r : ℕ} (hr : 2≤ r) (k : ℕ) :
    1≤ iwMultiplierConstant C r k := by
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hlog : (1/2 : ℝ)≤ Real.log (2+k : ℝ) :=
    real_log_two_half_le.trans (Real.log_le_log (by norm_num : (0 : ℝ)<2)
      (by have hk : (0 : ℝ)≤ k := Nat.cast_nonneg k;linarith))
  have hm : (4 : ℝ)≤ C*(r : ℝ) := by nlinarith
  have hbase : 1≤ C*(r : ℝ)*Real.log (2+k : ℝ) := by nlinarith
  unfold iwMultiplierConstant
  exact Real.one_le_rpow hbase (by positivity)

end PrimeSquares
