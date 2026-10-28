import PrimeSquares.CenteredExceptionalHigh
namespace PrimeSquares
theorem centeredExceptionalHigh_formula (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (θ : ℝ) :
    centeredExceptionalHigh N hN q₀ Q B χ κ β r θ=
      (κ r*rationalTwistedGauss r (χ r))*annularHighFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/B) θ*
        Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  simp only [centeredExceptionalHigh,ContinuousMap.sub_apply,
    centeredHighSymbol_mask_formula N hN q₀ hq₀ hQ hB]
  unfold rationalTwistedGauss
  ring
end PrimeSquares
