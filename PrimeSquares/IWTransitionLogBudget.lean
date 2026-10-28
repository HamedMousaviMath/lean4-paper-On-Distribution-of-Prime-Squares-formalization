import PrimeSquares.IWTransitionScale

set_option autoImplicit false
namespace PrimeSquares

theorem iw_period_log_bound {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) : Real.log (d.period : ℝ)≤2*(Q : ℝ) := by
  have hP : (0 : ℝ)< d.period := by exact_mod_cast d.period_pos
  have hb : (d.period : ℝ)≤(3 : ℝ)^Q := by exact_mod_cast d.period_bound
  have h := Real.log_le_log hP hb
  rw [Real.log_pow] at h
  have h3 : Real.log (3 : ℝ)≤2 := by
    simpa only [show (3 : ℝ)-1=2 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)
  have hm := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg Q : (0 : ℝ)≤ Q)
  nlinarith

theorem iw_narrow_log_inverse_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : TaoArcConstructionData C (iwRho k) k Q) :
    -Real.log (iwNarrowWidth (iwWidth C r k Q) d.period)≤
      100*((Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  have hε := iwWidth_pos hC hr k Q
  have hP : 1≤ d.period := by have h := d.period_pos;omega
  have hp := iwNarrowWidth_log_inverse hε hP
  have hloga := iwCutoffScale_log_bound hC hr hL
  have he : -Real.log (iwWidth C r k Q)=Real.log (iwCutoffScale C r k Q) := by
    rw [iwCutoffScale,Real.log_inv]
  have h16 : Real.log (16 : ℝ)≤15 := by
    simpa only [show (16 : ℝ)-1=15 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<16)
  have h100 : Real.log (100 : ℝ)≤99 := by
    simpa only [show (100 : ℝ)-1=99 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<100)
  have hperiod := iw_period_log_bound d
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  apply hp.trans
  apply max_le
  · rw [sub_eq_add_neg,he]
    nlinarith
  · nlinarith

theorem iw_transition_index_linear_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : TaoArcConstructionData C (iwRho k) k Q) :
    (iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ)+2≤
      101*((Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  let δ := iwNarrowWidth (iwWidth C r k Q) d.period
  have hδ0 : 0<δ := iwNarrowWidth_pos (iwWidth_pos hC hr k Q) (by have h := d.period_pos;omega)
  have hδ1 : δ≤1 := (iwNarrowWidth_small _ (by have h := d.period_pos;omega)).trans (by norm_num)
  have hj := (iwTransitionIndex_bounds hδ0 hδ1).2
  have hD : 0≤-Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ0.le hδ1)
  have hden : 1≤2*Real.log (2 : ℝ) := by linarith [real_log_two_half_le]
  have hdiv : (-Real.log δ)/(2*Real.log 2)≤-Real.log δ := by
    apply (div_le_iff₀ (by linarith : 0<2*Real.log (2 : ℝ))).mpr
    nlinarith
  have hb := iw_narrow_log_inverse_budget hC hr hQ hL d
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  dsimp only [δ] at hj hdiv
  linarith

theorem iw_transition_log_cost_budget {C : ℝ} (hC : 2≤ C) {r k Q : ℕ}
    (hr : 2≤ r) (hQ : 1≤ Q) (hL : 1≤ Real.log (iwDenominatorBound C k Q))
    (d : TaoArcConstructionData C (iwRho k) k Q) :
    Real.log (2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ))≤
      101*Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)) := by
  let U : ℝ := (Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q)
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ)≤ Q := by exact_mod_cast hQ
  have hRL : 2≤(r : ℝ)*Real.log (iwDenominatorBound C k Q) := by nlinarith
  have hU : 0< U := by dsimp [U];linarith
  have hb := iw_transition_index_linear_budget hC hr hQ hL d
  have hj : (0 : ℝ)<2+(iwTransitionIndex (iwNarrowWidth (iwWidth C r k Q) d.period) : ℝ) := by positivity
  have ht := Real.log_le_log hj (by simpa only [add_comm] using hb)
  rw [Real.log_mul (by norm_num : (101 : ℝ)≠0) hU.ne'] at ht
  have hc : Real.log (101 : ℝ)≤100 := by
    simpa only [show (101 : ℝ)-1=100 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<101)
  have hu : Real.log U≤ Real.log (Real.exp 1+U) := Real.log_le_log hU (by linarith [Real.exp_pos 1])
  have hl : 1≤ Real.log (Real.exp 1+U) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1≤ Real.exp 1+U by linarith)
    simpa only [Real.log_exp] using h
  dsimp [U] at hu hl ht
  rw [←add_assoc] at hu hl
  linarith

end PrimeSquares
