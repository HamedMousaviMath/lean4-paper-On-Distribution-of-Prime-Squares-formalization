import PrimeSquares.SourceHighPowerUniform
import PrimeSquares.QuantitativeErrorPairing

open Finset
namespace PrimeSquares

theorem sourceHigh_finite_pairing {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ) [NeZero q₀] (M : ℕ) (Γ : Finset ℚ),
      (∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M) →
    ∀ (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),0 ≤ β → β ≤ 1 →
      (∀ r ∈ Γ,‖κ r‖ ≤ 1) → ∀ F G : Finset ℤ,
      ‖∑ x ∈ G,circleHighOperator Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β (finiteIndicatorLp F 2) x‖ ≤
        H*Q^(-η)*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  obtain ⟨H,hH,h⟩ := sourceHigh_power_uniform hη0 hηhalf
  refine ⟨H,hH,?_⟩
  intro N hN Q hQ q₀ inst M Γ hΓ χ κ β hβ0 hβ1 hk F G
  exact operator_finite_indicator_pairing_bound _ (h N hN Q hQ q₀ M Γ hΓ χ κ β hβ0 hβ1 hk).2 F G

end PrimeSquares
