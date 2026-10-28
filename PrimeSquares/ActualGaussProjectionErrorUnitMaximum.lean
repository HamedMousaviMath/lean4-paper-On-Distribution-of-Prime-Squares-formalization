import PrimeSquares.ActualGaussProjectionErrorMaximum
import PrimeSquares.RationalGaussCoefficientUnitBounds
open scoped lp
namespace PrimeSquares
theorem actualGaussProjectionError_unit_maximum {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (hl : ∀ r ∈ Γ,Nat.log2 r.den=s)
    (χ : ℕ → ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ)
    (hκ : ∀ j,∀ r ∈ Γ,‖κ j r‖ ≤ 1)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier
        (circleMajorArcModel Γ ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)-
          rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (2*annularProjectionErrorL2Constant)*‖f‖ := by
  have hp : ∀ r ∈ Γ,‖rationalPrincipalGauss r‖ ≤ 1 := fun r hr =>
    (rationalGaussCoefficient_unit_bounds (χ 0) (κ 0) r (hκ 0 r hr)).1
  have he : ∀ j,∀ r ∈ Γ,‖rationalExceptionalCoefficient (χ j) (κ j) r‖ ≤ 1 :=
    fun j r hr => (rationalGaussCoefficient_unit_bounds (χ j) (κ j) r (hκ j r hr)).2
  simpa only [show (1 : ℝ)+1=2 by norm_num] using actualGaussProjectionError_maximum hM hs Γ hc hd hl
    χ κ β hβ0 hβ1 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hp he f
end PrimeSquares
