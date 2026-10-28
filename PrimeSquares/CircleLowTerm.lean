import PrimeSquares.CenteredHighSymbol
import PrimeSquares.CircleRationalModel

namespace PrimeSquares

noncomputable def circleLowTerm (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(PrimeCircle, ℂ) :=
  (compactCircleLift (centeredLowSymbol N hN q₀ Q B₀ χ κ β r)
    (centeredLowSymbol_support N hN q₀ Q B₀ χ κ β r)).comp
      ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩

theorem circleLowTerm_real (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    circleLowTerm N hN q₀ Q B₀ χ κ β r (ξ : PrimeCircle) =
      ∑' k : ℤ, centeredLowSymbol N hN q₀ Q B₀ χ κ β r (ξ-(r : ℝ)+k) := by
  change compactCircleLift (centeredLowSymbol N hN q₀ Q B₀ χ κ β r)
    (centeredLowSymbol_support N hN q₀ Q B₀ χ κ β r)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [← AddCircle.coe_sub]
  exact compactCircleLift_all_real _ _ _

end PrimeSquares
