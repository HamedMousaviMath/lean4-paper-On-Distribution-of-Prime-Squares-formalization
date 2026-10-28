import PrimeSquares.DyadicCollarConstant

namespace PrimeSquares

theorem rationalCollarBlock_power_energy {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ) (s : ℕ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {Q C δ : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ C*(r.den : ℝ)^(-δ))
    (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖rationalCollarBlock Γ ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j) θ‖^2) ≤
      ((192*C/(Real.pi*Q))*((2 : ℝ)^(1-δ))^s)^2 := by
  have hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1) := by
    intro r hr
    have hh : r.den ≤ (2 : ℕ)^(s+1) := by simpa only [hlog r hr] using (Nat.lt_log2_self (n := r.den)).le
    exact_mod_cast hh
  have hh := rationalCollarBlock_finite_energy hM Γ s hΓ hlog hQ hden β hβ0 hβ1 c
    (fun j r hr => dyadic_coefficient_power_budget (hlog r hr) hC hδ _ (hc j r hr)) J θ
  simpa only [dyadic_collar_constant_identity] using hh

end PrimeSquares
