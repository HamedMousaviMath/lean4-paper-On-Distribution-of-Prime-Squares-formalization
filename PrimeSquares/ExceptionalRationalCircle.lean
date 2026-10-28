import PrimeSquares.ExceptionalCenteredSupport
import PrimeSquares.CompactLiftExtensionality

namespace PrimeSquares

noncomputable def exceptionalRationalCircleLow (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q : ℝ) (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (r : ℚ) : C(PrimeCircle, ℂ) :=
  circleFrequencyShift (compactCircleLift (exceptionalCenteredLow N hN q₀ χ₀ Q β r)
    (exceptionalCenteredLow_support N hN (NeZero.pos q₀) χ₀ hQ hb β r)) (((r : ℝ) : PrimeCircle))

theorem exceptionalRationalCircleLow_not_dvd (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (r : ℚ) (hd : ¬q₀ ∣ r.den) : exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r=0 := by
  unfold exceptionalRationalCircleLow
  rw [compactCircleLift_congr _ _ _ (fun _ _ => rfl)
    (exceptionalCenteredLow_of_not_dvd N hN q₀ χ₀ Q β r hd)]
  erw [compactCircleLift_zero]
  exact circleFrequencyShift_zero _

theorem exceptionalRationalCircleLow_dvd (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (r : ℚ) (hd : q₀ ∣ r.den) :
    letI : NeZero r.den := ⟨r.den_pos.ne'⟩
    exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r=
      twistedSquareSum r.den (DirichletCharacter.changeLevel hd χ₀) (r.num : ZMod r.den) •
        circleFrequencyShift (circleAnnularCutoff N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (r.den/q₀ : ℕ))
          (exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ (NeZero.pos q₀))
            (by exact_mod_cast conductor_quotient_positive (NeZero.pos q₀) r.den_pos hd) hb)) (((r : ℝ) : PrimeCircle)) := by
  classical
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have hp := conductor_quotient_positive (NeZero.pos q₀) r.den_pos hd
  have ha := exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ (NeZero.pos q₀))
    (by exact_mod_cast hp : (1 : ℝ) ≤ (r.den/q₀ : ℕ)) hb
  have hc : exceptionalCenteredLow N hN q₀ χ₀ Q β r=
      twistedSquareSum r.den (DirichletCharacter.changeLevel hd χ₀) (r.num : ZMod r.den) •
        annularCutoffSymbol N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (r.den/q₀ : ℕ)) := by
    simp only [exceptionalCenteredLow,dite_eq_left hd]
  unfold exceptionalRationalCircleLow
  rw [compactCircleLift_congr _ _ _ (fun x hx => by
    change twistedSquareSum r.den (DirichletCharacter.changeLevel hd χ₀) (r.num : ZMod r.den)*
      annularCutoffSymbol N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (r.den/q₀ : ℕ)) x=0
    rw [annularCutoffSymbol_support N hN β ha x hx,mul_zero]) hc]
  exact shiftedAnnularLift_smul N hN β _ ha _ _ _

end PrimeSquares
