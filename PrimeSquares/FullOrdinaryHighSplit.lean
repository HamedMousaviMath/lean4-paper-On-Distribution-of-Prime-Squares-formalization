import PrimeSquares.LargeOrdinaryCircleModel

namespace PrimeSquares

theorem circleHighModel_ordinary_full_split (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q R B : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighModel (sourceRationalCenters R) N hN q₀ Q B χ (fun _ => 0) β=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss+
      circleMajorArcModel ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β := by
  rw [circleHighModel_denominator_split]
  rw [ordinaryHigh_filtered_source N hN q₀ hq₀ hQ hQR hB χ β]
  rw [circleHighModel_large_ordinary _ N hN q₀ Q B χ β (fun r hr => (Finset.mem_filter.mp hr).2)]

end PrimeSquares
