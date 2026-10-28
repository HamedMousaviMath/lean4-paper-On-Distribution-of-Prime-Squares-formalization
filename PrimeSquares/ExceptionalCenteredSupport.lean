import PrimeSquares.ExceptionalCenteredSource

namespace PrimeSquares

theorem exceptionalCenteredLow_support (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (r : ℚ) (θ : ℝ) (hθ : 1 ≤ |θ|) : exceptionalCenteredLow N hN q₀ χ₀ Q β r θ=0 := by
  classical
  by_cases hd : q₀ ∣ r.den
  · have : NeZero r.den := ⟨r.den_pos.ne'⟩
    have hp := conductor_quotient_positive hq₀ r.den_pos hd
    have ha := exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ hq₀)
      (by exact_mod_cast hp : (1 : ℝ) ≤ (r.den/q₀ : ℕ)) hb
    simp only [exceptionalCenteredLow,dite_eq_left hd]
    change twistedSquareSum r.den (DirichletCharacter.changeLevel hd χ₀) (r.num : ZMod r.den)*
      annularCutoffSymbol N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (r.den/q₀ : ℕ)) θ=0
    rw [annularCutoffSymbol_support N hN β ha θ hθ,mul_zero]
  · rw [exceptionalCenteredLow_of_not_dvd N hN q₀ χ₀ Q β r hd]
    rfl

end PrimeSquares
