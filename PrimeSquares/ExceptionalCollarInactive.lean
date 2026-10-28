import PrimeSquares.SourceHighOperatorFourPieces
namespace PrimeSquares
theorem rationalCollarBlock_inactive (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (W : ℝ)
    (β : ℚ → ℝ) (q₀ : ℕ) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) :
    rationalCollarBlock Γ N hN W β (fun r => sourceExceptionalSelector q₀ false r*rationalTwistedGauss r (χ r))=0 := by
  ext θ
  simp [rationalCollarBlock,sourceExceptionalSelector_inactive]
end PrimeSquares
