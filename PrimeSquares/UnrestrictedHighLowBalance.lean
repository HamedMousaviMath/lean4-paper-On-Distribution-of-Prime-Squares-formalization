import PrimeSquares.HighLowOptimization

/-! # The uniform two-term balance when every dyadic splitting parameter is available -/

namespace PrimeSquares

theorem unrestricted_highLow_scalar {s r γ β δ R C : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, 2 ≤ (2 : ℝ)^j → R ≤ C *
      (δ*((2 : ℝ)^j)^s*(Real.log ((2 : ℝ)^j))^γ +
        δ^(1/2 : ℝ)*((2 : ℝ)^j)^(-r)*(Real.log ((2 : ℝ)^j))^β)) :
    R ≤ C * highLowOptimizationConstant s r γ β * highLowEndpoint s r γ β δ := by
  let K₁ := (highLowLogScale s r)^γ + (2 : ℝ)^r*(highLowLogScale s r)^β
  let K₂ := (2 : ℝ)^s+1
  have hlog : 0 < highLowLogScale s r := lt_of_lt_of_le (by norm_num)
    (highLowLogScale_one_le hs hr)
  have h1 : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have h2 : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have h10 : 0 ≤ (10 : ℝ)^s := by positivity
  have h20 : 0 ≤ (20 : ℝ)^s := by positivity
  have hc1 : K₁ ≤ highLowOptimizationConstant s r γ β := by
    dsimp [highLowOptimizationConstant]
    change K₁ ≤ K₁+_+K₂+_
    linarith
  have hc2 : K₂ ≤ highLowOptimizationConstant s r γ β := by
    dsimp [highLowOptimizationConstant]
    change K₂ ≤ K₁+_+K₂+_
    linarith
  have hE := (highLowEndpoint_pos s r γ β hδ).le
  have enlarge : ∀ K : ℝ, K ≤ highLowOptimizationConstant s r γ β →
      R ≤ C*K*highLowEndpoint s r γ β δ →
      R ≤ C*highLowOptimizationConstant s r γ β*highLowEndpoint s r γ β δ := by
    intro K hK hR
    exact hR.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC) hE)
  by_cases hT : 2 ≤ highLowBalanceScale s r γ β δ
  · obtain ⟨j, hj, hjT, hTj⟩ := exists_dyadic_below hT
    apply enlarge K₁ hc1
    exact (hdec j hj).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (highLowBalance_nearby hs hr hβ hβγ hδ hδ1 hj hjT hTj.le) hC)
  · apply enlarge K₂ hc2
    have hd := hdec 1 (by norm_num)
    simp only [pow_one] at hd
    exact hd.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (highLowBalance_at_two hs hr hβ hβγ hδ hδ1 (le_of_not_ge hT)) hC)

end PrimeSquares
