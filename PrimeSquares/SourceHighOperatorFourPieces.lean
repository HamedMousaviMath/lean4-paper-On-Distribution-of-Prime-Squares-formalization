import PrimeSquares.SourceSixPieceSymbol
namespace PrimeSquares
theorem circleHighOperator_source_four_pieces (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hWR : effectiveCollarCutoff Q q₀ ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighOperator (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β=
      integerMultiplier (rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss)+
      integerMultiplier (circleMajorArcModel ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β)-
      (integerMultiplier (rationalCollarBlock (conductorCollarCenters Q q₀) N hN (effectiveCollarCutoff Q q₀) (fun _ => β)
        (fun r => sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r)))+
      integerMultiplier (circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => effectiveCollarCutoff Q q₀ < (r.den : ℝ)))
        N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β)) := by
  rw [circleHighOperator,circleHighModel_source_four_pieces N hN hq₀ hQ hQR hWR,
    integerMultiplier_sub,integerMultiplier_add,integerMultiplier_add]
end PrimeSquares
