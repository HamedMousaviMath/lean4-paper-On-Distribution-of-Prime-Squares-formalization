import PrimeSquares.RefinedTwistedCollarEnergy
open Finset
namespace PrimeSquares
theorem refinedTwistedCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hhalf : η+ε < 1/2) : ∃ H : ℝ,0 < H ∧
    ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r) →
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,‖κ j r‖ ≤ 1) →
    ∀ (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
        (fun r => κ j r*rationalTwistedGauss r (χ j r)) θ‖^2) ≤ (H*Q^(-η)*(q₀ : ℝ)^(-ε))^2 := by
  obtain ⟨H,hH,h⟩ := refinedTwistedCollar_energy_large hη hε hhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ β hβ0 hβ1 χ κ hk J θ
  by_cases hW : 1 ≤ effectiveCollarCutoff Q q₀
  · exact h M hM Q hQ q₀ hq₀ hW β hβ0 hβ1 χ κ hk J θ
  · rw [conductorCollarCenters_eq_empty (lt_of_not_ge hW)]
    simpa [rationalCollarBlock] using sq_nonneg (H*Q^(-η)*(q₀ : ℝ)^(-ε))
end PrimeSquares
