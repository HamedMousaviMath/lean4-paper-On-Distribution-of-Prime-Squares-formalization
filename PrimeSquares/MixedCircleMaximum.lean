import PrimeSquares.MixedCircleSquareEnergy
open scoped lp
namespace PrimeSquares
theorem mixed_circle_maximum {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (m : ℕ → ℕ → C(PrimeCircle,ℂ))
    (hE : ∀ i,∀ J : Finset ℕ,∀ θ : PrimeCircle,
      (∑ j ∈ J,‖m j i θ‖^2) ≤ (A*(q₀ i : ℝ)^(-ε))^2) (σ : ℕ → ℕ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (m j (σ j)) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ (∀ j x,‖integerMultiplier (m j (σ j)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ A*conductorClassEnergyConstant ε*‖f‖ := by
  exact circle_energy_maximal_witness _ (mul_nonneg hA (conductorClassEnergyConstant_pos hε).le)
    (mixed_circle_square_energy hε q₀ hclass m hE σ) f
end PrimeSquares
