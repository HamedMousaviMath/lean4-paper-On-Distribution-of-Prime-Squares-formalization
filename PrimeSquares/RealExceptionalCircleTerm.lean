import PrimeSquares.ExceptionalRationalCoordinates

namespace PrimeSquares

noncomputable def realExceptionalCircleTerm (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q : ℝ) (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) : C(PrimeCircle, ℂ) :=
  denominatorUnitSum q (fun r => exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r)

theorem realExceptionalCircleTerm_dvd (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) [NeZero q] (hdiv : q₀ ∣ q) :
    realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q=
      ∑ u : (ZMod q)ˣ,twistedSquareSum q (DirichletCharacter.changeLevel hdiv χ₀) u •
        circleFrequencyShift (circleAnnularCutoff N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (q/q₀ : ℕ))
          (exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ (NeZero.pos q₀))
            (by exact_mod_cast conductor_quotient_positive (NeZero.pos q₀) (NeZero.pos q) hdiv) hb))
          ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle) := by
  rw [realExceptionalCircleTerm,denominatorUnitSum_pos]
  apply Finset.sum_congr rfl
  intro u _
  exact exceptionalRationalCircleLow_unit N hN q₀ χ₀ hQ hb β q u hdiv

theorem realExceptionalCircleTerm_not_dvd (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) [NeZero q] (hd : ¬q₀ ∣ q) : realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q=0 := by
  rw [realExceptionalCircleTerm,denominatorUnitSum_pos]
  apply Finset.sum_eq_zero
  intro u _
  apply exceptionalRationalCircleLow_not_dvd N hN q₀ χ₀ hQ hb β (unitRational q u)
  simpa only [unitRational_den] using hd

end PrimeSquares
