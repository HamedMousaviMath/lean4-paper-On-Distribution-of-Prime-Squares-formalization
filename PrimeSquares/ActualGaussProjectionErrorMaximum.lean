import PrimeSquares.RationalGaussSmoothMainBlock
import PrimeSquares.SignedProjectionErrorMaximum
open scoped lp
namespace PrimeSquares
theorem actualGaussProjectionError_maximum {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (hl : ∀ r ∈ Γ,Nat.log2 r.den=s)
    (χ : ℕ → ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    {A₀ A₁ : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hp : ∀ r ∈ Γ,‖rationalPrincipalGauss r‖ ≤ A₀)
    (he : ∀ j,∀ r ∈ Γ,‖rationalExceptionalCoefficient (χ j) (κ j) r‖ ≤ A₁)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier
        (circleMajorArcModel Γ ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)-
          rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ ((A₀+A₁)*annularProjectionErrorL2Constant)*‖f‖ := by
  obtain ⟨g,hg,ht,hn⟩ := signedProjectionErrorBlock_maximum hM hs Γ hc hd
    (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j)
    (fun _ => rationalPrincipalGauss) (fun j => rationalExceptionalCoefficient (χ j) (κ j))
    hA₀ hA₁ (fun _ => hp) he f
  refine ⟨g,hg,?_,hn⟩
  intro j x
  have hi := circleMajorArcModel_smooth_error_blocks Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) s hl (χ j) (κ j) (β j)
  have hid : circleMajorArcModel Γ ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)-
      rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)=
      rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (fun _ => 1) rationalPrincipalGauss-
      rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (fun _ => β j)
        (rationalExceptionalCoefficient (χ j) (κ j)) := by rw [hi];abel
  rw [hid]
  exact ht j x
end PrimeSquares
