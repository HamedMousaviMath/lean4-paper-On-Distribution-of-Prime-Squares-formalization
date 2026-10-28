import PrimeSquares.UnrestrictedHighLowBalance

set_option autoImplicit false
namespace PrimeSquares

theorem highLowEndpoint_one_le {s r γ β δ : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hδ : 1 ≤ δ) : 1 ≤ highLowEndpoint s r γ β δ := by
  have hd := Real.one_le_rpow hδ (highLowDensityExponent_pos hs hr).le
  have hl := Real.one_le_rpow ((by norm_num : (1:ℝ)≤2).trans (paperLog_two_le δ))
    (highLowLogExponent_nonneg hs hr hγ hβ)
  exact one_le_mul_of_one_le_of_one_le hd hl

noncomputable def highLowCappedConstant (s r γ β cap : ℝ) : ℝ :=
  highLowOptimizationConstant s r γ β+
    cap*(2:ℝ)^s*(Real.log 2)^γ+
    cap^(1/2:ℝ)*(2:ℝ)^(-r)*(Real.log 2)^β+1

theorem unrestricted_highLow_scalar_capped {s r γ β δ cap R C : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hcap : δ ≤ cap) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, 2 ≤ (2:ℝ)^j → R ≤ C*
      (δ*((2:ℝ)^j)^s*(Real.log ((2:ℝ)^j))^γ+
        δ^(1/2:ℝ)*((2:ℝ)^j)^(-r)*(Real.log ((2:ℝ)^j))^β)) :
    R ≤ C*highLowCappedConstant s r γ β cap*highLowEndpoint s r γ β δ := by
  have hcapp : 0 < cap := hδ.trans_le hcap
  have hγ : 0 ≤ γ := hβ.trans hβγ
  have hlog : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hopt : 0 ≤ highLowOptimizationConstant s r γ β :=
    (highLowOptimizationConstant_pos hs hr γ β).le
  have hK : 0 ≤ highLowCappedConstant s r γ β cap := by
    unfold highLowCappedConstant
    positivity
  have he : 0 ≤ highLowEndpoint s r γ β δ := (highLowEndpoint_pos s r γ β hδ).le
  by_cases hδ1 : δ ≤ 1
  · apply (unrestricted_highLow_scalar hs hr hβ hβγ hδ hδ1 hC hdec).trans
    have hk : highLowOptimizationConstant s r γ β ≤ highLowCappedConstant s r γ β cap := by
      unfold highLowCappedConstant
      have h1 : 0 ≤ cap*(2:ℝ)^s*(Real.log 2)^γ := by positivity
      have h2 : 0 ≤ cap^(1/2:ℝ)*(2:ℝ)^(-r)*(Real.log 2)^β := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC) he
  · have hδge : 1 ≤ δ := (lt_of_not_ge hδ1).le
    have hraw := hdec 1 (by norm_num)
    simp only [pow_one] at hraw
    have hlower := highLowEndpoint_one_le hs hr hγ hβ hδge
    have hterm : δ*(2:ℝ)^s*(Real.log 2)^γ+
        δ^(1/2:ℝ)*(2:ℝ)^(-r)*(Real.log 2)^β ≤
        cap*(2:ℝ)^s*(Real.log 2)^γ+cap^(1/2:ℝ)*(2:ℝ)^(-r)*(Real.log 2)^β := by
      gcongr
    have hcrude : cap*(2:ℝ)^s*(Real.log 2)^γ+
        cap^(1/2:ℝ)*(2:ℝ)^(-r)*(Real.log 2)^β ≤ highLowCappedConstant s r γ β cap := by
      unfold highLowCappedConstant
      linarith
    exact (hraw.trans (mul_le_mul_of_nonneg_left (hterm.trans hcrude) hC)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlower (mul_nonneg hC hK))

end PrimeSquares
