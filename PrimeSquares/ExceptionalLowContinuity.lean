import PrimeSquares.OrdinaryLowContinuity

namespace PrimeSquares

theorem rationalExceptionalModelTerm_continuous {N : ℕ} (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    Continuous (rationalExceptionalModelTerm N χ κ β r) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  exact (continuous_const.mul (continuous_const.mul
    ((annularOscillatoryModel_continuous hN β).comp
      (continuous_id.sub continuous_const)))).neg

theorem exceptionalNarrowCutoff_continuous (N q₀ : ℕ) (Q B₀ : ℝ) (r : ℚ) :
    Continuous (exceptionalNarrowCutoff N q₀ Q B₀ r) := by
  apply Complex.continuous_ofReal.comp
  exact sourceArcCutoff_contDiff.continuous.comp
    (continuous_const.mul (continuous_id.sub continuous_const))

end PrimeSquares
