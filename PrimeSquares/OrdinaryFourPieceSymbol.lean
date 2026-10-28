import PrimeSquares.FullOrdinaryHighSplit

namespace PrimeSquares

theorem annularSymbol_ordinary_four_piece (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q R B : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt=
      circleLowModel (sourceRationalCenters R) N hN q₀ Q B χ (fun _ => 0) β+
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss+
      circleMajorArcModel ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β+
      circleMajorArcError (sourceRationalCenters R) N hN χ (fun _ => 0) β := by
  rw [annularSymbol_circle_low_high_error _ N hN q₀ Q B χ (fun _ => 0) β]
  rw [circleHighModel_ordinary_full_split N hN q₀ hq₀ hQ hQR hB χ β]
  simp only [add_assoc]

end PrimeSquares
