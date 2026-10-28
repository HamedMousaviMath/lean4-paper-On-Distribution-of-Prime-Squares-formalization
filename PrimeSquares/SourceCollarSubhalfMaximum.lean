import PrimeSquares.SourcePointwiseConvolutionBound
open scoped lp
namespace PrimeSquares
theorem sourceCollar_subhalf_maximum {η : ℝ} (hη : 0 ≤ η) (hηhalf : η < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,Q ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (f : ℓ²(ℤ,ℂ)),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (sourceCollarDifference ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) Q (R j) (q₀ (σ j))
        (active (σ j) j) (χ (σ j) j) (β (σ j) j)) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ (∀ j x,‖integerMultiplier (sourceCollarDifference ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) Q (R j) (q₀ (σ j))
        (active (σ j) j) (χ (σ j) j) (β (σ j) j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ K*Q^(-η)*‖f‖ := by
  obtain ⟨K,hK,h⟩ := combinedSourceCollar_maximum hη (by linarith : 0 < (1/2-η)/2)
    (by linarith : η+(1/2-η)/2 < 1/2)
  refine ⟨K,hK,?_⟩
  intro M hM Q hQ q₀ hclass R hQR active χ β hβ0 hβ1 σ f
  exact h M hM Q hQ q₀ hclass R (fun j => by linarith [hQR j]) active χ β hβ0 hβ1 σ f
end PrimeSquares
