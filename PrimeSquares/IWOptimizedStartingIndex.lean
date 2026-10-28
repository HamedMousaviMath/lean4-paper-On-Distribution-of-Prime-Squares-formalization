import PrimeSquares.IWOptimizedMaximalCost

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwRestrictedStartingIndex (C Cstart v : ℝ) : ℕ :=
  ⌈Cstart*iwRestrictedStartExpression C v/Real.log 2⌉₊+1

theorem iwRestrictedStartingIndex_admissible (C Cstart v : ℝ) :
    1 ≤ iwRestrictedStartingIndex C Cstart v ∧
      Real.exp (Cstart*iwRestrictedStartExpression C v) ≤
        (((2 : ℕ)^(iwRestrictedStartingIndex C Cstart v) : ℕ) : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := Nat.le_ceil (Cstart*iwRestrictedStartExpression C v/Real.log 2)
  have hJ : Cstart*iwRestrictedStartExpression C v ≤
      (iwRestrictedStartingIndex C Cstart v : ℝ)*Real.log 2 := by
    have h := (div_le_iff₀ hlog).mp hlo
    unfold iwRestrictedStartingIndex
    push_cast
    nlinarith
  refine ⟨by unfold iwRestrictedStartingIndex; omega, ?_⟩
  calc
    _ ≤ Real.exp ((iwRestrictedStartingIndex C Cstart v : ℝ)*Real.log 2) := Real.exp_le_exp.mpr hJ
    _ = _ := by rw [Nat.cast_pow, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

theorem iwRestrictedStartingIndex_exp_bound {C Cstart v : ℝ}
    (hC : 2 ≤ C) (hstart : 0 < Cstart) (hv : 1 ≤ v) :
    (iwRestrictedStartingIndex C Cstart v : ℝ) ≤
      (2*Cstart*iwOptimizedScaleCoefficient C+2)*Real.exp (384*nearOneCore v) := by
  have hS := iwRestrictedStartExpression_nonneg hC v
  have hlog := real_log_two_half_le
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 ≤ Cstart*iwRestrictedStartExpression C v/Real.log 2 := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  have hdiv : Cstart*iwRestrictedStartExpression C v/Real.log 2 ≤
      2*Cstart*iwRestrictedStartExpression C v := by
    apply (div_le_iff₀ hlogpos).mpr
    have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg hstart.le hS)
    nlinarith
  have hs := mul_le_mul_of_nonneg_left (iwRestrictedStartExpression_exp_bound hC hv)
    (show 0 ≤ 2*Cstart by positivity)
  have he : 1 ≤ Real.exp (384*nearOneCore v) :=
    Real.one_le_exp (mul_nonneg (by norm_num) (by linarith [(nearOneCore_basic_bounds hv).1]))
  unfold iwRestrictedStartingIndex
  push_cast
  nlinarith

end PrimeSquares
