import PrimeSquares.LocalizedModelContinuity

namespace PrimeSquares

theorem rationalOrdinaryModelTerm_continuous {N : ℕ} (hN : 1 ≤ N) (r : ℚ) :
    Continuous (rationalOrdinaryModelTerm N r) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  exact continuous_const.mul ((annularOscillatoryModel_continuous hN 1).comp
    (continuous_id.sub continuous_const))

theorem ordinaryNarrowCutoff_continuous (N : ℕ) (Q : ℝ) (r : ℚ) :
    Continuous (ordinaryNarrowCutoff N Q r) := by
  apply Complex.continuous_ofReal.comp
  exact sourceArcCutoff_contDiff.continuous.comp
    (continuous_const.mul (continuous_id.sub continuous_const))

end PrimeSquares
