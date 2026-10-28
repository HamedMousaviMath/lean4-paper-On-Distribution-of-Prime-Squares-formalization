import PrimeSquares.SharpHighExponentCoefficient
namespace PrimeSquares
theorem sharpHigh_source_log_loss {ε : ℝ} (hε : 0 < ε) (n : ℕ) (c : ℝ) :
    ∃ D : ℝ,0 < D ∧ ∀ Q : ℝ,2 ≤ Real.log Q →
      (1+Real.log Q)^n*Real.exp (c*sharpHighExponentWeight (Real.log Q)) ≤
        D*Real.exp ((c+ε)*sharpHighExponentWeight (Real.log Q)) := by
  obtain ⟨D,hD,h⟩ := sharpHigh_prefix_loss_coefficient hε n c
  exact ⟨D,hD,fun Q hQ => h (Real.log Q) hQ⟩
end PrimeSquares
