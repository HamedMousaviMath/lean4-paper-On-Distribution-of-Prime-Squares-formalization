import PrimeSquares.SourceCollarOutsideConductor
namespace PrimeSquares
noncomputable def sourceLargeHighRemainder (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (q₀ : ℕ)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) : C(PrimeCircle,ℂ) :=
  circleMajorArcModel ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β-
    circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => effectiveCollarCutoff Q q₀ < (r.den : ℝ)))
      N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β
theorem circleHighModel_collar_remainder (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hQR : Q ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β=
      sourceCollarDifference N hN Q R q₀ active χ β+sourceLargeHighRemainder N hN Q R q₀ active χ β := by
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  rw [circleHighModel_ordinary_sub_exceptional,circleHighModel_ordinary_full_split N hN q₀ hq₀ hQ hQR hB χ β,
    circleExceptionalHighModel_denominator_split _ N hN q₀ Q (conductorMajorant q₀) (effectiveCollarCutoff Q q₀)]
  unfold sourceCollarDifference sourceLargeHighRemainder
  ring
end PrimeSquares
