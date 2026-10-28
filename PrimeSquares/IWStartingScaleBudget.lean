import PrimeSquares.IWCommonCutoffTails

set_option autoImplicit false
namespace PrimeSquares

theorem iwDenominatorBound_log_one_le {C : ℝ} (hC : 2≤C) (hlogC : 1≤Real.log C)
    {k Q : ℕ} (hk : 4≤k) (hQ : 1≤Q) :
    1≤Real.log (iwDenominatorBound C k Q) := by
  have hkR : (4 : ℝ)≤k := by exact_mod_cast hk
  have hQpow : 1≤(Q : ℝ)^(1/((k : ℝ)-1/2)) :=
    Real.one_le_rpow (by exact_mod_cast hQ)
      (div_nonneg (by norm_num) (by linarith))
  rw [iwDenominatorBound_log (by linarith : 0<C)]
  have hk2 : (1 : ℝ)≤(k : ℝ)^2 := by nlinarith
  calc
    1 = 1*1*1 := by ring
    _ ≤ (k : ℝ)^2*(Q : ℝ)^(1/((k : ℝ)-1/2))*Real.log C := by gcongr

theorem iwCutoffScale_log_bound {C : ℝ} (hC : 2≤C) {r k Q : ℕ} (hr : 2≤r)
    (hlogB : 1≤Real.log (iwDenominatorBound C k Q)) :
    Real.log (iwCutoffScale C r k Q)≤17*(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by
  let B := iwDenominatorBound C k Q
  have hB : 1≤B := iwDenominatorBound_one_le hC k Q
  have hB0 : 0<B := by linarith
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have hr0 : (0 : ℝ)<r := by linarith
  have he : Real.log (iwCutoffScale C r k Q)=
      20*Real.log 2+Real.log (r : ℝ)+(2*(r : ℝ)+8)*Real.log B := by
    rw [iwCutoffScale_formula,Real.log_mul (by positivity : 2^20*(r : ℝ)≠0) (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ)^20≠0) hr0.ne',Real.log_pow,Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log (2 : ℝ)≤1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have hlogr : Real.log (r : ℝ)≤r :=
    (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
  have hRL : (r : ℝ)≤(r : ℝ)*Real.log B := le_mul_of_one_le_right hr0.le hlogB
  have hcoef : (2*(r : ℝ)+8)*Real.log B≤6*(r : ℝ)*Real.log B := by
    have hm := mul_le_mul_of_nonneg_right (show 2*(r : ℝ)+8≤6*(r : ℝ) by linarith)
      (show 0≤Real.log B by linarith)
    nlinarith
  rw [he]
  nlinarith

theorem iw_starting_budget_exp_bound {C : ℝ} (hC : 2≤C) {r k Q : ℕ}
    (hr : 2≤r) (hQ : 1≤Q) (hlogB : 1≤Real.log (iwDenominatorBound C k Q)) :
    ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ)≤
      Real.exp (25*((Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q))) := by
  let a := iwCutoffScale C r k Q
  let L := Real.log (iwDenominatorBound C k Q)
  have hQ1 : (1 : ℝ)≤Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ)<Q := by linarith
  have ha : 0<a := (by norm_num : (0 : ℝ)<4).trans_le (iwCutoffScale_four_le hC hr k Q)
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have hRL : 2≤(r : ℝ)*L := by nlinarith
  have hlogQ : Real.log ((Q : ℝ)+1)≤1+Real.log Q := by
    have hm := Real.log_le_log (by positivity : (0 : ℝ)<(Q : ℝ)+1)
      (show (Q : ℝ)+1≤2*(Q : ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hQ0.ne'] at hm
    have hlog2 : Real.log (2 : ℝ)≤1 := by
      simpa only [show (2 : ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hloga : Real.log a≤17*(r : ℝ)*L := iwCutoffScale_log_bound hC hr hlogB
  have hY : 0<((Q : ℝ)+1)^2*a*(Q : ℝ) := by positivity
  have hlogY : Real.log (((Q : ℝ)+1)^2*a*(Q : ℝ))≤
      25*((Real.log (Q : ℝ))^2+(r : ℝ)*L) := by
    rw [Real.log_mul (by positivity : ((Q : ℝ)+1)^2*a≠0) hQ0.ne',
      Real.log_mul (by positivity : ((Q : ℝ)+1)^2≠0) ha.ne',Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [sq_nonneg (Real.log (Q : ℝ)-1)]
  calc
    _ = Real.exp (Real.log (((Q : ℝ)+1)^2*a*(Q : ℝ))) := (Real.exp_log hY).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlogY

theorem iw_starting_budget_of_source_scale {C : ℝ} (hC : 2≤C) (hCe : Real.exp 1≤C)
    {r k Q M : ℕ} (hr : 2≤r) (hk : 4≤k) (hQ : 1≤Q) (hM : 2≤M)
    (hstart : Real.exp (25*((Real.log (Q : ℝ))^2+
      (r : ℝ)*Real.log (iwDenominatorBound C k Q)))≤M) :
    ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ)≤(M : ℝ)^2 := by
  have hlogC : 1≤Real.log C := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hCe
  have hlogB := iwDenominatorBound_log_one_le hC hlogC hk hQ
  have h := (iw_starting_budget_exp_bound hC hr hQ hlogB).trans hstart
  have hMr : (2 : ℝ)≤M := by exact_mod_cast hM
  exact h.trans (by nlinarith)

end PrimeSquares
