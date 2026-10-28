import PrimeSquares.AllCutoffTwistedCollarEnergy
open scoped lp
namespace PrimeSquares
theorem refinedTwistedCollar_maximum {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hhalf : η+ε < 1/2) : ∃ H : ℝ,0 < H ∧
    ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r) →
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,‖κ j r‖ ≤ 1) →
    ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
        (fun r => κ j r*rationalTwistedGauss r (χ j r))) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ (∀ j x,‖integerMultiplier (rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
        (fun r => κ j r*rationalTwistedGauss r (χ j r))) f x‖ ≤ g x) ∧
      ‖g‖ ≤ H*Q^(-η)*(q₀ : ℝ)^(-ε)*‖f‖ := by
  obtain ⟨H,hH,h⟩ := refinedTwistedCollar_energy hη hε hhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ β hβ0 hβ1 χ κ hk f
  exact circle_energy_maximal_witness _ (by positivity) (h M hM Q hQ q₀ hq₀ β hβ0 hβ1 χ κ hk) f
end PrimeSquares
