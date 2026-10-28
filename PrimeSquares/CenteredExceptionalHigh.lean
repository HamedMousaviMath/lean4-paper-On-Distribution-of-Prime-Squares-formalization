import PrimeSquares.RefinedTwistedCollarPairing
namespace PrimeSquares
noncomputable def centeredExceptionalHigh (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(ℝ,ℂ) :=
  centeredHighSymbol N hN q₀ Q B χ (fun _ => 0) β r-centeredHighSymbol N hN q₀ Q B χ κ β r
theorem centeredExceptionalHigh_support (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (θ : ℝ)
    (hθ : 1 ≤ |θ|) : centeredExceptionalHigh N hN q₀ Q B χ κ β r θ=0 := by
  simp only [centeredExceptionalHigh,ContinuousMap.sub_apply,centeredHighSymbol_support N hN q₀ Q B χ (fun _ => 0) β r θ hθ,
    centeredHighSymbol_support N hN q₀ Q B χ κ β r θ hθ,sub_self]
end PrimeSquares
