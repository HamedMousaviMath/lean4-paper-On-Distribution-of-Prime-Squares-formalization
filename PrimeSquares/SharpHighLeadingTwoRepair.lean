import PrimeSquares.SharpHighSourceLogLoss
namespace PrimeSquares
theorem sharpHigh_leading_two_prefix_repair {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ Q : ℝ,0 < Q → 2 ≤ Real.log Q →
      Q^(-(1/2 : ℝ))*(1+Real.log Q)^n*Real.exp (2*sharpHighExponentWeight (Real.log Q)) ≤
        D*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)) := by
  obtain ⟨D,hD,h⟩ := sharpHigh_source_log_loss hε n 2
  refine ⟨D,hD,?_⟩
  intro Q hQp hQ
  have he := mul_le_mul_of_nonneg_left (h Q hQ) (Real.rpow_pos_of_pos hQp (-(1/2 : ℝ))).le
  convert he using 1 <;> ring
end PrimeSquares
