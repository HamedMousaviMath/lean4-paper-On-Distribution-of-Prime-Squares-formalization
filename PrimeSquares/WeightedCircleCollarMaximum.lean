import PrimeSquares.WeightedCircleCollarEnergy

open scoped lp
namespace PrimeSquares

theorem circleAnnularCollar_weighted_maximum {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q b : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (hb : 0 ≤ b) (s : ℕ) (center : ℝ) (c : ℕ → ℂ) (hc : ∀ j,‖c j‖ ≤ b) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (c j • circleAnnularCollar ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s center) f x‖) ∧
      ‖g‖ ≤ b*(24*q/(Real.pi*Q))*‖f‖ := by
  exact circle_symbol_countable_maximal _ (by positivity) (circleAnnularCollar_weighted_energy hM β hβ0 hβ1 hq hQ s center c hc) f

end PrimeSquares
