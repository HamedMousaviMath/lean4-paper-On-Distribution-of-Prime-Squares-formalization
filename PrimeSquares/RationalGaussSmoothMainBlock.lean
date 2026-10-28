import PrimeSquares.CircleGaussSmoothErrorDecomposition
import PrimeSquares.RationalProjectionErrorBlock
import PrimeSquares.FiniteCircleModel
open Finset
namespace PrimeSquares
noncomputable def rationalGaussSmoothMainBlock (Γ : Finset ℚ) (N s : ℕ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,(rationalPrincipalGauss r*annularOscillatoryModel N 1 0-
    rationalExceptionalCoefficient χ κ r*annularOscillatoryModel N β 0) • circleAnnularSmoothProjection N s r
theorem circleMajorArcModel_smooth_error_blocks (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (s : ℕ)
    (hl : ∀ r ∈ Γ,Nat.log2 r.den=s)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleMajorArcModel Γ N hN χ κ β=rationalGaussSmoothMainBlock Γ N s χ κ β+
      rationalProjectionErrorBlock Γ N hN s (fun _ => 1) rationalPrincipalGauss-
      rationalProjectionErrorBlock Γ N hN s (fun _ => β) (rationalExceptionalCoefficient χ κ) := by
  unfold circleMajorArcModel rationalGaussSmoothMainBlock rationalProjectionErrorBlock
  rw [←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro r hr
  rw [circleRationalModel_smooth_error_decomposition,hl r hr]
end PrimeSquares
