import PrimeSquares.ChangingSourceCollarEnergy
open scoped lp
namespace PrimeSquares
theorem changingSourceCollar_maximum {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (f : ℓ²(ℤ,ℂ)),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (circleExceptionalHighModel ((sourceRationalCenters (R j)).filter
        (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q (q₀ (σ j)))) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ (σ j)) Q (conductorMajorant (q₀ (σ j)))
        (χ (σ j) j) (sourceExceptionalSelector (q₀ (σ j)) (active (σ j) j)) (β (σ j) j)) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ ‖g‖ ≤ K*Q^(-η)*‖f‖ := by
  obtain ⟨K,hK,h⟩ := changingSourceCollar_energy hη hε hhalf
  refine ⟨K,hK,?_⟩
  intro M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ f
  obtain ⟨g,hg,hg0,_,hn⟩ := circle_energy_maximal_witness _ (by positivity)
    (h M hM Q hQ q₀ hclass R hR active χ β hβ0 hβ1 σ) f
  exact ⟨g,hg,hg0,hn⟩
end PrimeSquares
