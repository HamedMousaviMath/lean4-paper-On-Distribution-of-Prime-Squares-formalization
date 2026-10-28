import PrimeSquares.QuantitativeIWBalance
import PrimeSquares.IWTransitionScale

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwRestrictedOrder (v : ℝ) : ℕ := ⌈v⌉₊+2
noncomputable def iwRestrictedCutoff (v : ℝ) : ℕ := (2 : ℕ)^(4*iwRestrictedOrder v)

theorem iwRestrictedOrder_bounds {v : ℝ} (hv : 1 ≤ v) :
    2 ≤ iwRestrictedOrder v ∧ v+2 ≤ (iwRestrictedOrder v : ℝ) ∧
      (iwRestrictedOrder v : ℝ) ≤ v+3 ∧ (iwRestrictedOrder v : ℝ) ≤ 4*v := by
  have hlo := Nat.le_ceil v
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ v by linarith)
  refine ⟨by unfold iwRestrictedOrder; omega, ?_, ?_, ?_⟩
  all_goals unfold iwRestrictedOrder; push_cast; linarith

theorem iwRestrictedRank_bounds {v : ℝ} (hv : 1 ≤ v) :
    4 ≤ iwBalancedRank v ∧ (iwBalancedRank v : ℝ) ≤ v+5 ∧
      (iwBalancedRank v : ℝ) ≤ 7*v := by
  obtain ⟨hk, _hlo, hhi⟩ := iwBalancedRank_bounds hv
  have hL := (nearOne_innerLog_bounds hv).1
  have hLp : 0 < Real.log (Real.exp 1+v) := by linarith
  have hquot : v/Real.log (Real.exp 1+v) ≤ v^2 := by
    apply (div_le_iff₀ hLp).mpr
    have hm := mul_le_mul_of_nonneg_left hL (sq_nonneg v)
    nlinarith
  have hs := Real.sq_sqrt (div_nonneg (show 0 ≤ v by linarith) hLp.le)
  have hs0 := Real.sqrt_nonneg (v/Real.log (Real.exp 1+v))
  have hroot : Real.sqrt (v/Real.log (Real.exp 1+v)) ≤ v := by nlinarith
  refine ⟨hk, by linarith, by linarith⟩

theorem iwRestrictedCutoff_log (v : ℝ) :
    Real.log (iwRestrictedCutoff v : ℝ) = 4*(iwRestrictedOrder v : ℝ)*Real.log 2 := by
  unfold iwRestrictedCutoff
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

theorem iwRestrictedCutoff_bounds {v : ℝ} (hv : 1 ≤ v) :
    (2 : ℕ)^(iwBalancedRank v) ≤ iwRestrictedCutoff v ∧
      2*v ≤ Real.log (iwRestrictedCutoff v : ℝ) ∧
      Real.log (iwRestrictedCutoff v : ℝ) ≤ 16*v := by
  have hr := iwRestrictedOrder_bounds hv
  have hk := iwRestrictedRank_bounds hv
  have hkr : iwBalancedRank v ≤ 4*iwRestrictedOrder v := by
    exact_mod_cast (show (iwBalancedRank v : ℝ) ≤ 4*(iwRestrictedOrder v : ℝ) by linarith [hk.2.1, hr.2.1])
  have hloglo := real_log_two_half_le
  have hloghi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hmlo := mul_le_mul_of_nonneg_left hloglo (show 0 ≤ 4*(iwRestrictedOrder v : ℝ) by positivity)
  have hmhi := mul_le_mul_of_nonneg_left hloghi (show 0 ≤ 4*(iwRestrictedOrder v : ℝ) by positivity)
  refine ⟨Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hkr, ?_, ?_⟩
  all_goals rw [iwRestrictedCutoff_log]; linarith [hr.2.1, hr.2.2.2]

theorem iwRestricted_near_one_power {t : ℝ} (ht : 1 ≤ t) :
    t^(iwNearOneExponent (iwRestrictedOrder (nearOneLog t))-1) ≤ Real.exp 1 := by
  have ht0 : 0 < t := by linarith
  have hv := nearOneLog_one_le t
  have hr := iwRestrictedOrder_bounds hv
  have hlog : Real.log t ≤ nearOneLog t := by
    unfold nearOneLog
    rw [max_eq_right (by linarith : 0 ≤ t)]
    exact Real.log_le_log ht0 (by have he := Real.exp_pos (1 : ℝ); linarith)
  have hden : 0 < 2*(iwRestrictedOrder (nearOneLog t) : ℝ)-1 := by linarith [hr.2.1]
  have hlogden : Real.log t ≤ 2*(iwRestrictedOrder (nearOneLog t) : ℝ)-1 := by linarith [hr.2.1]
  rw [iwNearOneExponent_sub_one hr.1, Real.rpow_def_of_pos ht0]
  apply Real.exp_le_exp.mpr
  simpa only [mul_one_div] using (div_le_one hden).mpr hlogden

theorem iwRestricted_high_cost {t : ℝ} (ht : 1 ≤ t) :
    t*(iwRestrictedCutoff (nearOneLog t) : ℝ)^(-(1/2 : ℝ)) ≤ 1 := by
  let v := nearOneLog t
  have hv : 1 ≤ v := nearOneLog_one_le t
  have hq := (iwRestrictedCutoff_bounds hv).2.1
  have hQp : (0 : ℝ) < iwRestrictedCutoff v := by dsimp [iwRestrictedCutoff]; positivity
  have hdecay : (iwRestrictedCutoff v : ℝ)^(-(1/2 : ℝ)) ≤ Real.exp (-v) := by
    rw [Real.rpow_def_of_pos hQp]
    exact Real.exp_le_exp.mpr (by linarith)
  have htExp : t ≤ Real.exp v := by
    have he : Real.exp v = Real.exp 1+t := by
      dsimp [v, nearOneLog]
      rw [max_eq_right (by linarith : 0 ≤ t), Real.exp_log (by positivity)]
    rw [he]
    have h := Real.exp_pos (1 : ℝ)
    linarith
  calc
    _ ≤ t*Real.exp (-v) := mul_le_mul_of_nonneg_left hdecay (by linarith)
    _ = t/Real.exp v := by rw [Real.exp_neg, div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (Real.exp_pos v)).mpr htExp

theorem iwRestricted_two_t_power {t : ℝ} (ht : 1 ≤ t) :
    (2*t)^(iwNearOneExponent (iwRestrictedOrder (nearOneLog t))) ≤ 4*Real.exp 1*t := by
  let p := iwNearOneExponent (iwRestrictedOrder (nearOneLog t))
  have ht0 : 0 < t := by linarith
  have hr := (iwRestrictedOrder_bounds (nearOneLog_one_le t)).1
  have hp := iwNearOneExponent_bounds hr
  have h2 : (2 : ℝ)^p ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [p]; linarith [hp.2])
      _ = 4 := by norm_num
  have htp : t^p = t*t^(p-1) := by
    calc
      t^p = t^(1+(p-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add ht0, Real.rpow_one]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0.le, htp]
  calc
    _ ≤ 4*(t*Real.exp 1) := mul_le_mul h2
      (mul_le_mul_of_nonneg_left (iwRestricted_near_one_power ht) ht0.le) (by positivity) (by norm_num)
    _ = _ := by ring

end PrimeSquares
