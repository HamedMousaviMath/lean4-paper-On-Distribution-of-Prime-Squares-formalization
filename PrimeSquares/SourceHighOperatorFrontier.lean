import PrimeSquares.SourceLargeHighRemainder
namespace PrimeSquares
theorem circleHighOperator_collar_remainder (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hQR : Q ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighOperator (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β=
      integerMultiplier (sourceCollarDifference N hN Q R q₀ active χ β)+
      integerMultiplier (sourceLargeHighRemainder N hN Q R q₀ active χ β) := by
  rw [circleHighOperator,circleHighModel_collar_remainder N hN hQ hq₀ hQR,integerMultiplier_add]
end PrimeSquares
