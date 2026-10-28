import PrimeSquares.OrdinaryCenteredLowSource

namespace PrimeSquares

noncomputable def ordinaryRationalCircleLow (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (r : ℚ) : C(PrimeCircle, ℂ) :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  principalSquareSum r.den (r.num : ZMod r.den) •
    circleFrequencyShift (circleAnnularCutoff N hN 1 (ordinaryLowWidth N Q r.den)
      (ordinaryLowWidth_two_le hQ (by exact_mod_cast r.den_pos) hb)) (((r : ℝ) : PrimeCircle))

theorem ordinaryCenteredLow_circle (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (r : ℚ) :
    circleFrequencyShift (compactCircleLift (ordinaryCenteredLow N hN Q r)
      (ordinaryCenteredLow_support N hN hQ hb r)) (((r : ℝ) : PrimeCircle))=
      ordinaryRationalCircleLow N hN Q hQ hb r := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha := ordinaryLowWidth_two_le hQ (by exact_mod_cast r.den_pos : (1 : ℝ) ≤ r.den) hb
  change circleFrequencyShift (compactCircleLift
    (principalSquareSum r.den (r.num : ZMod r.den) • annularCutoffSymbol N hN 1 (ordinaryLowWidth N Q r.den)) _)
    (((r : ℝ) : PrimeCircle))=_
  erw [compactCircleLift_smul _ _ (annularCutoffSymbol_support N hN 1 ha) _]
  rw [circleFrequencyShift_smul]
  rfl

end PrimeSquares
