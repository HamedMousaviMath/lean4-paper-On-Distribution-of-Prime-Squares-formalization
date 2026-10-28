import PrimeSquares.ConductorClassSquareDecay
import PrimeSquares.GeometricPowerBudget
open Finset
namespace PrimeSquares
theorem finite_conductor_class_budget {ε : ℝ} (hε : 0 < ε) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (S : Finset ℕ) :
    (∑ i ∈ S,((q₀ i : ℝ)^(-ε))^2) ≤ (1-(2 : ℝ)^(-(2*ε)))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(-(2*ε)) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ)^(-(2*ε)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc
    _ ≤ ∑ i ∈ S,((2 : ℝ)^(-(2*ε)))^i := sum_le_sum (fun i _ => conductor_class_square_decay hε.le q₀ hclass i)
    _ ≤ ∑' i : ℕ,((2 : ℝ)^(-(2*ε)))^i := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum S (fun _ _ => by positivity)
    _ = _ := tsum_geometric_of_lt_one hr0 hr1
end PrimeSquares
