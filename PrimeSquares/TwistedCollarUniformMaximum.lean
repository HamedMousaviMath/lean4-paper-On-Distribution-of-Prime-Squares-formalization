import PrimeSquares.OrdinaryCollarUniformMaximum

open scoped lp
namespace PrimeSquares

theorem twistedCollar_uniform_maximum {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q → ∀ Γ : Finset ℚ,
      (∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊Q⌋₊) →
    ∀ (β : ℕ → ℚ → ℝ),(∀ j,∀ r ∈ Γ,0 ≤ β j r) → (∀ j,∀ r ∈ Γ,β j r ≤ 1) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
      (∀ j,∀ r ∈ Γ,‖κ j r‖ ≤ 1) → ∀ f : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (rationalCollarBlock Γ ((2 : ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (fun r => κ j r*rationalTwistedGauss r (χ j r))) f x‖) ∧
        ‖g‖ ≤ H*Q^(-δ)*‖f‖ := by
  obtain ⟨C,hC,hG⟩ := rationalGauss_uniform_decay hδhalf
  have hδ1 : δ < 1 := by linarith
  refine ⟨collarPowerConstant C δ,collarPowerConstant_pos hC hδ1,?_⟩
  intro M hM Q hQ Γ hΓ β hβ0 hβ1 χ κ hk f
  apply completeRationalCollar_countable_maximum hM Γ (fun r hr => (hΓ r hr).1) hQ hC hδ0 hδ1
    (fun r hr => (hΓ r hr).2) β hβ0 hβ1 (fun j r => κ j r*rationalTwistedGauss r (χ j r)) _ f
  intro j r hr
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_right (hk j r hr) (norm_nonneg _)).trans (by simp)).trans ((hG r).2 (χ j r))

end PrimeSquares
