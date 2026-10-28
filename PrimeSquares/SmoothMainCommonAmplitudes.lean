import PrimeSquares.RationalGaussSmoothMainBlock
open Finset
namespace PrimeSquares
theorem rationalGaussSmoothMain_common_amplitudes (Γ : Finset ℚ) (N s : ℕ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ→ℂ) (β : ℝ) :
    rationalGaussSmoothMainBlock Γ N s χ κ β=
      annularOscillatoryModel N 1 0 • (∑ r∈Γ,rationalPrincipalGauss r • circleAnnularSmoothProjection N s r)-
      annularOscillatoryModel N β 0 • (∑ r∈Γ,rationalExceptionalCoefficient χ κ r • circleAnnularSmoothProjection N s r) := by
  unfold rationalGaussSmoothMainBlock
  rw [smul_sum,smul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro r hr
  ext θ
  simp only [ContinuousMap.smul_apply,ContinuousMap.sub_apply,smul_eq_mul]
  ring
end PrimeSquares
