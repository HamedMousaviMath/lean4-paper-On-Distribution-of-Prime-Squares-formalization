import PrimeSquares.ConductorCollarConstantBudget
open Finset
namespace PrimeSquares
theorem refinedTwistedCollar_energy_large {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hhalf : η+ε < 1/2) : ∃ H : ℝ,0 < H ∧
    ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),0 < Q → ∀ (q₀ : ℕ),0 < q₀ →
    1 ≤ effectiveCollarCutoff Q q₀ →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r) →
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ conductorCollarCenters Q q₀,‖κ j r‖ ≤ 1) →
    ∀ (J : Finset ℕ) (θ : PrimeCircle),
      (∑ j ∈ J,‖rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j)
        (fun r => κ j r*rationalTwistedGauss r (χ j r)) θ‖^2) ≤ (H*Q^(-η)*(q₀ : ℝ)^(-ε))^2 := by
  obtain ⟨C,hC,hG⟩ := conductorGauss_envelope hε hhalf
  obtain ⟨T,hT,hRatio⟩ := conductorMajorant_ratio_uniform
  have hη1 : η < 1 := by linarith
  refine ⟨collarPowerConstant C η*T^η,by have hp := collarPowerConstant_pos hC hη1;positivity,?_⟩
  intro M hM Q hQ q₀ hq₀ hW β hβ0 hβ1 χ κ hk J θ
  have he := conductorCollar_envelope_energy (ε := ε) hM hC hη hη1 hq₀ hW β hβ0 hβ1
    (fun j r => κ j r*rationalTwistedGauss r (χ j r)) (fun j r hr => ?_) J θ
  · exact he.trans (pow_le_pow_left₀ (by have hp := collarPowerConstant_pos hC hη1;positivity)
      (conductorCollar_constant_budget hQ hC hη hη1 hq₀ (hRatio q₀ hq₀)) 2)
  · rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right (hk j r hr) (norm_nonneg _)).trans (by simp)).trans
      (hG q₀ hq₀ r (mem_conductorCollarCenters.mp hr).2.2 (χ j r))
end PrimeSquares
