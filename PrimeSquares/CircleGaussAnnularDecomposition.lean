import PrimeSquares.CenteredGaussAnnularDecomposition
import PrimeSquares.CircleRationalModel
import PrimeSquares.CircleAnnularSource
namespace PrimeSquares
theorem circleRationalModel_annular_decomposition (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    circleRationalModelTerm N hN χ κ β r=
      rationalPrincipalGauss r • circleAnnularSource N hN 1 (Nat.log2 r.den) r-
        rationalExceptionalCoefficient χ κ r • circleAnnularSource N hN β (Nat.log2 r.den) r := by
  ext θ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) (θ-((r : ℝ) : PrimeCircle)) : ℝ)
  change compactPeriodWindow (centeredRationalSymbol N hN χ κ β r) x=
    rationalPrincipalGauss r*compactPeriodWindow (localizedAnnularSource N hN 1 (Nat.log2 r.den)) x-
      rationalExceptionalCoefficient χ κ r*compactPeriodWindow (localizedAnnularSource N hN β (Nat.log2 r.den)) x
  rw [centeredRationalSymbol_annular_decomposition]
  simp only [compactPeriodWindow,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring
end PrimeSquares
