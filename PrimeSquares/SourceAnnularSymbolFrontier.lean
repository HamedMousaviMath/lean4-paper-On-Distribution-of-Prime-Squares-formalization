import PrimeSquares.SourceFiniteConvolutionFrontier
namespace PrimeSquares
theorem annularSymbol_source_frontier (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hQR : Q ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt=
      circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β+
      sourceCollarDifference N hN Q R q₀ active χ β+
      sourceLargeHighRemainder N hN Q R q₀ active χ β+
      circleMajorArcError (sourceRationalCenters R) N hN χ (sourceExceptionalSelector q₀ active) β := by
  rw [annularSymbol_circle_low_high_error (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β,
    circleHighModel_collar_remainder N hN hQ hq₀ hQR]
  abel
end PrimeSquares
