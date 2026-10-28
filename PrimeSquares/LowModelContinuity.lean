import PrimeSquares.ExceptionalLowContinuity

namespace PrimeSquares

theorem rationalLowModelTerm_continuous {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    Continuous (rationalLowModelTerm N q₀ Q B₀ χ κ β r) := by
  classical
  have ho := (rationalOrdinaryModelTerm_continuous hN r).mul
    (ordinaryNarrowCutoff_continuous N Q r)
  have he := (rationalExceptionalModelTerm_continuous hN χ κ β r).mul
    (exceptionalNarrowCutoff_continuous N q₀ Q B₀ r)
  unfold rationalLowModelTerm
  split_ifs
  · exact ho.add he
  · exact ho.add continuous_const
  · exact continuous_const.add he
  · exact continuous_const

end PrimeSquares
