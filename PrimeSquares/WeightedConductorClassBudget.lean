import PrimeSquares.ConductorClassEnergyConstant
open Finset
namespace PrimeSquares
theorem weighted_conductor_class_budget {ε A : ℝ} (hε : 0 < ε) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (S : Finset ℕ) :
    (∑ i ∈ S,(A*(q₀ i : ℝ)^(-ε))^2) ≤ (A*conductorClassEnergyConstant ε)^2 := by
  simp_rw [mul_pow]
  rw [←mul_sum,conductorClassEnergyConstant_sq hε]
  exact mul_le_mul_of_nonneg_left (finite_conductor_class_budget hε q₀ hclass S) (sq_nonneg A)
end PrimeSquares
