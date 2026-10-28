import PrimeSquares.DifferenceCircleEnergy
namespace PrimeSquares
noncomputable def sourceCollarDifference (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (q₀ : ℕ)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) : C(PrimeCircle,ℂ) :=
  rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss-
    circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀))
      N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β
theorem sourceCollarDifference_apply (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (q₀ : ℕ)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (θ : PrimeCircle) :
    sourceCollarDifference N hN Q R q₀ active χ β θ=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss θ-
      circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀))
        N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β θ := rfl
end PrimeSquares
