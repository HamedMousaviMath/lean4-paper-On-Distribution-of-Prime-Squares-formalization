import PrimeSquares.ActualGaussProjectionErrorUnitMaximum
import PrimeSquares.FiniteMultiplierMaximalCriterion
import PrimeSquares.SourceDyadicDenominatorBounds
open scoped lp
namespace PrimeSquares
theorem sourceBlock_maximum_from_smooth_finite {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hΓ : Γ ⊆ sourceDyadicRationalCenters s)
    (χ : ℕ → ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ)
    (hκ : ∀ j,∀ r ∈ Γ,‖κ j r‖ ≤ 1)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hmain : ∀ J : Finset ℕ,∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j ∈ J,∀ x,‖integerMultiplier (rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s
        (χ j) (κ j) (β j)) f x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖f‖)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (B+2*annularProjectionErrorL2Constant)*‖f‖ := by
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := finite_multiplier_countable_maximum
    (fun j => rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) hB hmain f
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := actualGaussProjectionError_unit_maximum hM hs Γ
    (fun r hr => ((mem_sourceDyadicRationalCenters s r).mp (hΓ hr)).1)
    (fun _ hr => (sourceDyadicRationalCenters_den_bounds (hΓ hr)).2.le)
    (fun r hr => ((mem_sourceDyadicRationalCenters s r).mp (hΓ hr)).2) χ κ hκ β hβ0 hβ1 f
  refine ⟨g₀+g₁,fun x => add_nonneg (hg₀ x) (hg₁ x),?_,?_⟩
  · intro j x
    have heq : integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)) f=
        integerMultiplier (rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) f+
          integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) (χ j) (κ j) (β j)-
            rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) f := by
      rw [integerMultiplier_sub]
      simp only [_root_.sub_apply]
      abel
    rw [heq]
    change ‖integerMultiplier _ f x+integerMultiplier _ f x‖ ≤ g₀ x+g₁ x
    exact (norm_add_le _ _).trans (add_le_add (ht₀ j x) (ht₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hn₀ hn₁).trans_eq (by ring))
end PrimeSquares
