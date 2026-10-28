import PrimeSquares.CenteredHighPowerBound

namespace PrimeSquares

theorem centeredHighSymbol_zero_of_broad (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (θ : ℝ)
    (hz : sourceArcCutoffScale (Nat.log2 r.den) θ=0) : centeredHighSymbol N hN q₀ Q B χ κ β r θ=0 := by
  simp [centeredHighSymbol,centeredRationalSymbol,localizedAnnularGaussModel,centeredLowSymbol,hz]

end PrimeSquares
