import PrimeSquares.ExceptionalMultipleReindexing
import PrimeSquares.OrdinaryCenteredLowSource

namespace PrimeSquares

noncomputable def exceptionalCenteredLow (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ)
    (χ₀ : DirichletCharacter ℂ q₀) (Q β : ℝ) (r : ℚ) : C(ℝ, ℂ) :=
  if hd : q₀ ∣ r.den then
    letI : NeZero r.den := ⟨r.den_pos.ne'⟩
    twistedSquareSum r.den (DirichletCharacter.changeLevel hd χ₀) (r.num : ZMod r.den) •
      annularCutoffSymbol N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (r.den/q₀ : ℕ))
  else 0

theorem exceptionalCenteredLow_of_not_dvd (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ)
    (χ₀ : DirichletCharacter ℂ q₀) (Q β : ℝ) (r : ℚ) (h : ¬q₀ ∣ r.den) :
    exceptionalCenteredLow N hN q₀ χ₀ Q β r=0 := by
  simp only [exceptionalCenteredLow,dite_eq_right h]

end PrimeSquares
