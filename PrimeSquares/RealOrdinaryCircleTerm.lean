import PrimeSquares.OrdinaryRationalUnitSymbol

namespace PrimeSquares

noncomputable def realOrdinaryCircleTerm (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q : ℕ) : C(PrimeCircle, ℂ) :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ,principalSquareSum q u •
      circleFrequencyShift (circleAnnularCutoff N hN 1 (ordinaryLowWidth N Q q)
        (ordinaryLowWidth_two_le hQ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq) hb))
        ((((u : ZMod q).val : ℝ)/(q : ℝ)) : PrimeCircle)

theorem denominatorUnitSum_ordinary (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q : ℕ) :
    denominatorUnitSum q (fun r => ordinaryRationalCircleLow N hN Q hQ hb r)=
      realOrdinaryCircleTerm N hN Q hQ hb q := by
  classical
  by_cases hq : q=0
  · simp only [denominatorUnitSum,realOrdinaryCircleTerm,dite_eq_left hq]
  · have : NeZero q := ⟨hq⟩
    simp only [denominatorUnitSum,realOrdinaryCircleTerm,dite_eq_right hq]
    apply Finset.sum_congr rfl
    intro u _
    exact ordinaryRationalCircleLow_unit N hN hQ hb q u

end PrimeSquares
