import PrimeSquares.WeightedConductorClassBudget
open Finset
namespace PrimeSquares
theorem mixed_circle_square_energy {ε A : ℝ} (hε : 0 < ε) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (m : ℕ → ℕ → C(PrimeCircle,ℂ))
    (hE : ∀ i,∀ J : Finset ℕ,∀ θ : PrimeCircle,
      (∑ j ∈ J,‖m j i θ‖^2) ≤ (A*(q₀ i : ℝ)^(-ε))^2) (σ : ℕ → ℕ)
    (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖m j (σ j) θ‖^2) ≤ (A*conductorClassEnergyConstant ε)^2 := by
  exact (disjoint_time_square_energy (fun j i => m j i θ) _ (fun i I => hE i I θ) σ J).trans
    (weighted_conductor_class_budget hε q₀ hclass (J.image σ))
end PrimeSquares
