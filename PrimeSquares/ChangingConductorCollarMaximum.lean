import PrimeSquares.ChangingConductorCollarEnergy
open scoped lp
namespace PrimeSquares
theorem changingConductorCollar_maximum {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (hhalf : η+ε < 1/2) :
    ∃ K : ℝ,0 < K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) →
    ∀ (β : ℕ → ℕ → ℚ → ℝ),
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),0 ≤ β i j r) →
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),β i j r ≤ 1) →
    ∀ (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℕ → ℚ → ℂ),
      (∀ i j,∀ r ∈ conductorCollarCenters Q (q₀ i),‖κ i j r‖ ≤ 1) →
    ∀ (σ : ℕ → ℕ) (f : ℓ²(ℤ,ℂ)),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier
        (dyadicConductorCollar M hM Q (q₀ (σ j)) (β (σ j)) (χ (σ j)) (κ (σ j)) j) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ (∀ j x,‖integerMultiplier
        (dyadicConductorCollar M hM Q (q₀ (σ j)) (β (σ j)) (χ (σ j)) (κ (σ j)) j) f x‖ ≤ g x) ∧
      ‖g‖ ≤ K*Q^(-η)*‖f‖ := by
  obtain ⟨K,hK,h⟩ := changingConductorCollar_energy hη hε hhalf
  refine ⟨K,hK,?_⟩
  intro M hM Q hQ q₀ hclass β hβ0 hβ1 χ κ hk σ f
  exact circle_energy_maximal_witness _ (by positivity) (h M hM Q hQ q₀ hclass β hβ0 hβ1 χ κ hk σ) f
end PrimeSquares
