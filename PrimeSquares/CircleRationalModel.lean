import PrimeSquares.CenteredRationalSymbol
import PrimeSquares.CompactCirclePeriodization

namespace PrimeSquares

noncomputable def circleRationalModelTerm (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    C(PrimeCircle, ℂ) :=
  (compactCircleLift (centeredRationalSymbol N hN χ κ β r)
    (centeredRationalSymbol_support N hN χ κ β r)).comp
      ⟨fun θ => θ-((r : ℝ) : PrimeCircle), continuous_id.sub continuous_const⟩

theorem circleRationalModelTerm_real (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    circleRationalModelTerm N hN χ κ β r (ξ : PrimeCircle) =
      ∑' k : ℤ, centeredRationalSymbol N hN χ κ β r (ξ-(r : ℝ)+k) := by
  change compactCircleLift (centeredRationalSymbol N hN χ κ β r)
    (centeredRationalSymbol_support N hN χ κ β r)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [← AddCircle.coe_sub]
  exact compactCircleLift_all_real _ _ _

theorem circleRationalModelTerm_local (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) {ξ : ℝ}
    (hx : ξ-(r : ℝ) ∈ Set.Ico (-(1/2) : ℝ) (1/2)) :
    circleRationalModelTerm N hN χ κ β r (ξ : PrimeCircle) =
      compactPeriodWindow (centeredRationalSymbol N hN χ κ β r) (ξ-(r : ℝ)) := by
  change compactCircleLift (centeredRationalSymbol N hN χ κ β r)
    (centeredRationalSymbol_support N hN χ κ β r)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [← AddCircle.coe_sub]
  exact compactCircleLift_real _ _ hx

end PrimeSquares
