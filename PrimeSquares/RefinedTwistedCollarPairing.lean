import PrimeSquares.RefinedTwistedCollarMaximum
open Finset
namespace PrimeSquares
theorem refinedTwistedCollar_indicator_pairing {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hhalf : η+ε < 1/2) : ∃ H : ℝ,0 < H ∧
    ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r) →
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,‖κ j r‖ ≤ 1) →
    ∀ F G : Finset ℤ,
      (∑ x ∈ G,⨆ j : ℕ,‖integerMultiplier (rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
        (fun r => κ j r*rationalTwistedGauss r (χ j r))) (finiteIndicatorLp F 2) x‖) ≤
      H*Q^(-η)*(q₀ : ℝ)^(-ε)*Real.sqrt F.card*Real.sqrt G.card := by
  obtain ⟨H,hH,h⟩ := refinedTwistedCollar_energy hη hε hhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ q₀ hq₀ β hβ0 hβ1 χ κ hk F G
  obtain ⟨g,hg,_,hb⟩ := circle_energy_indicator_maximal_pairing _ (by positivity)
    (h M hM Q hQ q₀ hq₀ β hβ0 hβ1 χ κ hk) F
  simpa only [hg] using hb G
end PrimeSquares
