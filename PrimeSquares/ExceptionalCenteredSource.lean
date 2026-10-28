import PrimeSquares.ExceptionalCenteredLow

namespace PrimeSquares

theorem exceptionalCenteredLow_source (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    (χ₀ : DirichletCharacter ℂ q₀) (Q β : ℝ) (active : Bool) (r : ℚ) (θ : ℝ) :
    rationalExceptionalModelTerm N (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active)
      β r (θ+(r : ℝ))*exceptionalNarrowCutoff N q₀ Q (conductorMajorant q₀) r (θ+(r : ℝ))=
      -(if active=true then exceptionalCenteredLow N hN q₀ χ₀ Q β r θ else 0) := by
  classical
  by_cases ha : active=true
  · by_cases hd : q₀ ∣ r.den
    · have hc := conductor_quotient_real hq₀ hd
      simp [rationalExceptionalModelTerm,sourceExceptionalSelector,sourceInducedCharacter,
        exceptionalCenteredLow,exceptionalNarrowCutoff,ha,hd,annularCutoffSymbol,exceptionalLowWidth,hc,mul_assoc]
    · simp [rationalExceptionalModelTerm,sourceExceptionalSelector,exceptionalCenteredLow,ha,hd]
  · simp [rationalExceptionalModelTerm,sourceExceptionalSelector,ha]

end PrimeSquares
