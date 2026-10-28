import PrimeSquares.CircleShiftAlgebra
import PrimeSquares.LowWidthLowerBounds
import PrimeSquares.SourceExceptionalUnitData

namespace PrimeSquares

noncomputable def ordinaryCenteredLow (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (r : ℚ) : C(ℝ, ℂ) :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  principalSquareSum r.den (r.num : ZMod r.den) •
    annularCutoffSymbol N hN 1 (ordinaryLowWidth N Q r.den)

theorem ordinaryCenteredLow_source (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (r : ℚ) (θ : ℝ) :
    ordinaryCenteredLow N hN Q r θ=
      rationalOrdinaryModelTerm N r (θ+(r : ℝ))*ordinaryNarrowCutoff N Q r (θ+(r : ℝ)) := by
  dsimp [ordinaryCenteredLow,annularCutoffSymbol,rationalOrdinaryModelTerm,ordinaryNarrowCutoff,ordinaryLowWidth]
  rw [add_sub_cancel_right]
  ring

theorem ordinaryCenteredLow_support (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (r : ℚ) (θ : ℝ) (hθ : 1 ≤ |θ|) : ordinaryCenteredLow N hN Q r θ=0 := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha := ordinaryLowWidth_two_le hQ (by exact_mod_cast r.den_pos : (1 : ℝ) ≤ r.den) hb
  change principalSquareSum r.den (r.num : ZMod r.den)*annularCutoffSymbol N hN 1 (ordinaryLowWidth N Q r.den) θ=0
  rw [annularCutoffSymbol_support N hN 1 ha θ hθ,mul_zero]

end PrimeSquares
