import PrimeSquares.CenteredLowSymbol

namespace PrimeSquares

noncomputable def centeredHighSymbol (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(ℝ, ℂ) :=
  centeredRationalSymbol N hN χ κ β r - centeredLowSymbol N hN q₀ Q B₀ χ κ β r

theorem centeredHighSymbol_support (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ)
    (θ : ℝ) (hθ : 1 ≤ |θ|) : centeredHighSymbol N hN q₀ Q B₀ χ κ β r θ = 0 := by
  simp only [centeredHighSymbol,ContinuousMap.sub_apply,
    centeredRationalSymbol_support N hN χ κ β r θ hθ,
    centeredLowSymbol_support N hN q₀ Q B₀ χ κ β r θ hθ,sub_self]

theorem centeredModel_low_add_high (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    centeredLowSymbol N hN q₀ Q B₀ χ κ β r + centeredHighSymbol N hN q₀ Q B₀ χ κ β r =
      centeredRationalSymbol N hN χ κ β r := add_sub_cancel _ _

end PrimeSquares
