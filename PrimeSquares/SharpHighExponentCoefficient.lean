import PrimeSquares.SharpHighPrefixLossAbsorption
namespace PrimeSquares
theorem sharpHigh_prefix_loss_coefficient {ε : ℝ} (hε : 0 < ε) (n : ℕ) (c : ℝ) :
    ∃ D : ℝ,0 < D ∧ ∀ L : ℝ,2 ≤ L →
      (1+L)^n*Real.exp (c*sharpHighExponentWeight L) ≤ D*Real.exp ((c+ε)*sharpHighExponentWeight L) := by
  obtain ⟨D,hD,h⟩ := sharpHigh_shifted_polynomial_absorption hε n
  refine ⟨D,hD,?_⟩
  intro L hL
  calc
    _ ≤ (D*Real.exp (ε*sharpHighExponentWeight L))*Real.exp (c*sharpHighExponentWeight L) :=
      mul_le_mul_of_nonneg_right (h L hL) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
end PrimeSquares
