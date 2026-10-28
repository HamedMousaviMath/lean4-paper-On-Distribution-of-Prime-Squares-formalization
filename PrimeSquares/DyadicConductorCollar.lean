import PrimeSquares.MixedCircleMaximum
namespace PrimeSquares
noncomputable def dyadicConductorCollar (M : ℕ) (hM : 2 ≤ M) (Q : ℝ) (q₀ : ℕ)
    (β : ℕ → ℚ → ℝ) (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ)
    (j : ℕ) : C(PrimeCircle,ℂ) :=
  rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
    (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
    (fun r => κ j r*rationalTwistedGauss r (χ j r))
theorem dyadicConductorCollar_energy {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hhalf : η+ε < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r) →
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,‖κ j r‖ ≤ 1) →
    ∀ (J : Finset ℕ) (θ : PrimeCircle),(∑ j ∈ J,‖dyadicConductorCollar M hM Q q₀ β χ κ j θ‖^2) ≤
      (H*Q^(-η)*(q₀ : ℝ)^(-ε))^2 := by
  exact refinedTwistedCollar_energy hη hε hhalf
end PrimeSquares
