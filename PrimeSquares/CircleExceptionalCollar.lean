import PrimeSquares.CircleExceptionalHigh
namespace PrimeSquares
theorem circleExceptionalHigh_collar (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hr : (r.den : ℝ) ≤ Q*(q₀ : ℝ)/B) :
    circleExceptionalHigh N hN q₀ Q B χ κ β r=
      (κ r*rationalTwistedGauss r (χ r)) • circleAnnularCollar N hN β (r.den : ℝ) (Q*(q₀ : ℝ)/B) (Nat.log2 r.den) (r : ℝ) := by
  ext θ
  change compactPeriodWindow (centeredExceptionalHigh N hN q₀ Q B χ κ β r) _=
    (κ r*rationalTwistedGauss r (χ r))*compactPeriodWindow (annularCollarSymbol N hN β (r.den : ℝ) (Q*(q₀ : ℝ)/B) (Nat.log2 r.den)) _
  rw [centeredExceptionalHigh_collar N hN hq₀ hQ hB χ κ β r hr]
  simp only [compactPeriodWindow,ContinuousMap.smul_apply,smul_eq_mul]
  ring
end PrimeSquares
