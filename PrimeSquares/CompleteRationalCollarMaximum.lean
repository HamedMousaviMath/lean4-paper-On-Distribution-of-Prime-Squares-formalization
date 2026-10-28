import PrimeSquares.CompleteRationalCollarEnergy

open scoped lp
namespace PrimeSquares

theorem completeRationalCollar_countable_maximum {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) {Q C δ : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 < C) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hden : ∀ r ∈ Γ,r.den ≤ ⌊Q⌋₊)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ C*(r.den : ℝ)^(-δ)) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (rationalCollarBlock Γ ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j)) f x‖) ∧
      ‖g‖ ≤ collarPowerConstant C δ*Q^(-δ)*‖f‖ := by
  have hp := collarPowerConstant_pos hC hδ1
  exact circle_symbol_countable_maximal _ (by positivity)
    (completeRationalCollar_finite_energy hM Γ hΓ hQ hC hδ0 hδ1 hden β hβ0 hβ1 c hc) f

end PrimeSquares
