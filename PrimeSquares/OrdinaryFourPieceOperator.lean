import PrimeSquares.OrdinaryFourPieceSymbol

open scoped lp
namespace PrimeSquares

theorem annularOperator_ordinary_four_piece (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q R B : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt=
      integerMultiplier (circleLowModel (sourceRationalCenters R) N hN q₀ Q B χ (fun _ => 0) β)+
      integerMultiplier (rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss)+
      circleMajorArcOperator ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β+
      circleMajorArcErrorOperator (sourceRationalCenters R) N hN χ (fun _ => 0) β := by
  rw [annularWeightedSquareAverage_l2_multiplier,annularSymbol_ordinary_four_piece N hN q₀ hq₀ hQ hQR hB χ β]
  simp only [integerMultiplier_add,circleMajorArcOperator,circleMajorArcErrorOperator]

end PrimeSquares
