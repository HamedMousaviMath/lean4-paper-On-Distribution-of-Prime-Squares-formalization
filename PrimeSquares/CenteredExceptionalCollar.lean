import PrimeSquares.CenteredExceptionalHighFormula
namespace PrimeSquares
theorem centeredExceptionalHigh_collar (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hr : (r.den : ℝ) ≤ Q*(q₀ : ℝ)/B) :
    centeredExceptionalHigh N hN q₀ Q B χ κ β r=
      (κ r*rationalTwistedGauss r (χ r)) • annularCollarSymbol N hN β (r.den : ℝ) (Q*(q₀ : ℝ)/B) (Nat.log2 r.den) := by
  ext θ
  rw [centeredExceptionalHigh_formula N hN hq₀ hQ hB χ κ β r θ,annularHighFactor_eq_collar hr]
  change (κ r*rationalTwistedGauss r (χ r))*annularCollarFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/B) θ*_= _*(annularCollarFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/B) θ*_)
  ring
end PrimeSquares
