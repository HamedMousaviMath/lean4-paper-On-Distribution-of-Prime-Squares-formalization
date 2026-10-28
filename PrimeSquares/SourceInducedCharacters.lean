import PrimeSquares.SourceExceptionalSelector
import PrimeSquares.InducedIntegerCorrelation

namespace PrimeSquares

noncomputable def sourceInducedCharacter (q₀ : ℕ) (χ₀ : DirichletCharacter ℂ q₀) (r : ℚ) :
    DirichletCharacter ℂ r.den :=
  if h : q₀ ∣ r.den then DirichletCharacter.changeLevel h χ₀ else 1

theorem sourceInducedCharacter_of_dvd (q₀ : ℕ) (χ₀ : DirichletCharacter ℂ q₀) (r : ℚ)
    (h : q₀ ∣ r.den) : sourceInducedCharacter q₀ χ₀ r=DirichletCharacter.changeLevel h χ₀ := by
  simp only [sourceInducedCharacter,dite_eq_left h]

theorem sourceInducedCharacter_of_not_dvd (q₀ : ℕ) (χ₀ : DirichletCharacter ℂ q₀) (r : ℚ)
    (h : ¬q₀ ∣ r.den) : sourceInducedCharacter q₀ χ₀ r=1 := by
  simp only [sourceInducedCharacter,dite_eq_right h]

end PrimeSquares
