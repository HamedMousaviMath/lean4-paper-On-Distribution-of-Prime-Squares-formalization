import PrimeSquares.IntegerWindowSupport
import PrimeSquares.FiniteCircleHighLow

namespace PrimeSquares

theorem circleHighTerm_unit_window (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ)
    (hr : r ∈ Set.Ico (0 : ℚ) 1) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    circleHighTerm N hN q₀ Q B χ κ β r (ξ : PrimeCircle)=
      compactPeriodWindow (centeredHighSymbol N hN q₀ Q B χ κ β r) (ξ-(r : ℝ)) := by
  rw [circleHighTerm_real]
  have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr.1
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr.2
  exact integerPeriodSum_unit_window _ (centeredHighSymbol_support N hN q₀ Q B χ κ β r)
    ⟨by linarith [hξ.1],by linarith [hξ.2]⟩

end PrimeSquares
