import PrimeSquares.SharpHighPolynomialAbsorption
namespace PrimeSquares
theorem sharpHigh_shifted_polynomial_absorption {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ L : ℝ,2 ≤ L → (1+L)^n ≤ D*Real.exp (ε*sharpHighExponentWeight L) := by
  obtain ⟨D,hD,h⟩ := sharpHigh_polynomial_absorption hε (n : ℝ)
  refine ⟨(2 : ℝ)^n*D,by positivity,?_⟩
  intro L hL
  calc
    _ ≤ (2*L)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
    _ = (2 : ℝ)^n*L^n := mul_pow _ _ _
    _ ≤ (2 : ℝ)^n*(D*Real.exp (ε*sharpHighExponentWeight L)) := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_natCast] using h L hL) (by positivity)
    _ = _ := by ring
end PrimeSquares
