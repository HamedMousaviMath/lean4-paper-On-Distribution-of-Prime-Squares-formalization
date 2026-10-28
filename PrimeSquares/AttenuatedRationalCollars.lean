import PrimeSquares.RationalCollarBlockMaximum

open scoped lp
namespace PrimeSquares

theorem rationalCollarBlock_attenuated_maximum {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ) (s : ℕ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {Q b U : ℝ} (hQ : 0 < Q) (hb : 0 ≤ b) (hU : 0 ≤ U) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ U)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ b) (n : ℕ → C(PrimeCircle,ℂ))
    (hn : ∀ j,∀ θ,‖n j θ‖ ≤ ‖rationalCollarBlock Γ ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j) θ‖) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (n j) f x‖) ∧ ‖g‖ ≤ (96*b*U/(Real.pi*Q))*‖f‖ := by
  exact circle_symbol_attenuated_maximal _ n (by positivity)
    (rationalCollarBlock_finite_energy hM Γ s hΓ hlog hQ hden β hβ0 hβ1 c hc) hn f

end PrimeSquares
