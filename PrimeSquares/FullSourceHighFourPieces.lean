import PrimeSquares.LargeExceptionalHighModel
namespace PrimeSquares
theorem circleHighModel_source_four_pieces (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hWR : effectiveCollarCutoff Q q₀ ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss+
      circleMajorArcModel ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β-
      (rationalCollarBlock (conductorCollarCenters Q q₀) N hN (effectiveCollarCutoff Q q₀) (fun _ => β)
        (fun r => sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r))+
      circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => effectiveCollarCutoff Q q₀ < (r.den : ℝ)))
        N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β) := by
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  rw [circleHighModel_ordinary_sub_exceptional,circleHighModel_ordinary_full_split N hN q₀ hq₀ hQ hQR hB χ β,
    circleExceptionalHighModel_denominator_split _ N hN q₀ Q (conductorMajorant q₀) (effectiveCollarCutoff Q q₀),
    source_exceptional_collar_identity N hN hQ hq₀ hWR]
end PrimeSquares
