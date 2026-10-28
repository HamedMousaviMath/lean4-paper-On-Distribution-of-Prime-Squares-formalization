import PrimeSquares.ExceptionalRationalCircle

namespace PrimeSquares

theorem exceptionalRationalCircleLow_coordinates (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (r : ℚ) (q : ℕ) [NeZero q] (u : (ZMod q)ˣ)
    (hd : r.den=q) (hn : r.num=((u : ZMod q).val : ℤ))
    (hc : (r : ℝ)=((u : ZMod q).val : ℝ)/(q : ℝ)) (hdiv : q₀ ∣ q) :
    exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r=
      twistedSquareSum q (DirichletCharacter.changeLevel hdiv χ₀) u •
        circleFrequencyShift (circleAnnularCutoff N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (q/q₀ : ℕ))
          (exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ (NeZero.pos q₀))
            (by exact_mod_cast conductor_quotient_positive (NeZero.pos q₀) (NeZero.pos q) hdiv) hb))
          ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle) := by
  subst q
  rw [exceptionalRationalCircleLow_dvd N hN q₀ χ₀ hQ hb β r hdiv]
  simp only [hn,Int.cast_natCast,ZMod.natCast_zmod_val,hc]

theorem exceptionalRationalCircleLow_unit (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) (hdiv : q₀ ∣ q) :
    exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β (unitRational q u)=
      twistedSquareSum q (DirichletCharacter.changeLevel hdiv χ₀) u •
        circleFrequencyShift (circleAnnularCutoff N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) (q/q₀ : ℕ))
          (exceptionalLowWidth_two_le hQ (conductorMajorant_one_le q₀ (NeZero.pos q₀))
            (by exact_mod_cast conductor_quotient_positive (NeZero.pos q₀) (NeZero.pos q) hdiv) hb))
          ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle) :=
  exceptionalRationalCircleLow_coordinates N hN q₀ χ₀ hQ hb β (unitRational q u) q u
    (unitRational_den q u) (unitRational_num q u) (unitRational_real q u) hdiv

end PrimeSquares
