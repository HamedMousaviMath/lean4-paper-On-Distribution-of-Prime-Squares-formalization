import PrimeSquares.OrdinaryRationalCircleSource

namespace PrimeSquares

theorem ordinaryRationalCircleLow_coordinates (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (r : ℚ) (q : ℕ) [NeZero q] (u : (ZMod q)ˣ)
    (hd : r.den=q) (hn : r.num=((u : ZMod q).val : ℤ))
    (hc : (r : ℝ)=((u : ZMod q).val : ℝ)/(q : ℝ)) :
    ordinaryRationalCircleLow N hN Q hQ hb r=principalSquareSum q u •
      circleFrequencyShift (circleAnnularCutoff N hN 1 (ordinaryLowWidth N Q q)
        (ordinaryLowWidth_two_le hQ (by exact_mod_cast NeZero.pos q) hb))
        ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle) := by
  subst q
  simp only [ordinaryRationalCircleLow,hn,Int.cast_natCast,ZMod.natCast_zmod_val,hc]

theorem ordinaryRationalCircleLow_unit (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    ordinaryRationalCircleLow N hN Q hQ hb (unitRational q u)=principalSquareSum q u •
      circleFrequencyShift (circleAnnularCutoff N hN 1 (ordinaryLowWidth N Q q)
        (ordinaryLowWidth_two_le hQ (by exact_mod_cast NeZero.pos q) hb))
        ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle) :=
  ordinaryRationalCircleLow_coordinates N hN hQ hb (unitRational q u) q u
    (unitRational_den q u) (unitRational_num q u) (unitRational_real q u)

end PrimeSquares
