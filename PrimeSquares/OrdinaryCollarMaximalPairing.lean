import PrimeSquares.TwistedGaussCollarEnergy

open Finset
open scoped lp
namespace PrimeSquares

theorem ordinaryCollar_uniform_maximal_pairing {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q → ∀ Γ : Finset ℚ,
      (∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊Q⌋₊) →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ Γ,0 ≤ β j r) → (∀ j,∀ r ∈ Γ,β j r ≤ 1) →
    ∀ κ : ℕ → ℚ → ℂ,(∀ j,∀ r ∈ Γ,‖κ j r‖ ≤ 1) → ∀ F : Finset ℤ,
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (rationalCollarBlock Γ ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (fun r => κ j r*rationalPrincipalGauss r))
          (finiteIndicatorLp F 2) x‖) ∧
        (∀ j x,‖integerMultiplier (rationalCollarBlock Γ ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (fun r => κ j r*rationalPrincipalGauss r))
          (finiteIndicatorLp F 2) x‖ ≤ g x) ∧
        ∀ G : Finset ℤ,(∑ x ∈ G,g x) ≤ H*Q^(-δ)*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  obtain ⟨H,hH,he⟩ := ordinaryGaussCollar_uniform_energy hδ0 hδhalf
  refine ⟨H,hH,?_⟩
  intro M hM Q hQ Γ hΓ β hβ0 hβ1 κ hk F
  have hQp : 0 < Q := by linarith
  exact circle_energy_indicator_maximal_pairing _ (by positivity)
    (he M hM Q hQ Γ hΓ β hβ0 hβ1 κ hk) F

end PrimeSquares
