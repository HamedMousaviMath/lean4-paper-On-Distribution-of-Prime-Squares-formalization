import PrimeSquares.CircleGaussAnnularDecomposition
import PrimeSquares.CircleAnnularSourceDecomposition
namespace PrimeSquares
theorem circleRationalModel_smooth_error_decomposition (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    circleRationalModelTerm N hN χ κ β r=
      (rationalPrincipalGauss r*annularOscillatoryModel N 1 0-
        rationalExceptionalCoefficient χ κ r*annularOscillatoryModel N β 0) •
          circleAnnularSmoothProjection N (Nat.log2 r.den) r+
      rationalPrincipalGauss r • circleAnnularProjectionError N hN 1 (Nat.log2 r.den) r-
        rationalExceptionalCoefficient χ κ r • circleAnnularProjectionError N hN β (Nat.log2 r.den) r := by
  rw [circleRationalModel_annular_decomposition,circleAnnularSource_decomposition,
    circleAnnularSource_decomposition]
  ext θ
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring
end PrimeSquares
