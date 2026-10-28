import PrimeSquares.WeightedDisjointPrefix
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem weightedMultiplier_interval_budget (a K : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (c : ℕ → ℂ) {A : ℝ} (hc : ∀ i,‖c i‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    intervalRealBudget a K (fun i => ‖integerMultiplier (c i • m i) f‖^2) ≤
      A^2*intervalRealBudget a K (fun i => ‖integerMultiplier (m i) f‖^2) := by
  unfold intervalRealBudget
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  dsimp only
  rw [integerMultiplier_smul,_root_.smul_apply,norm_smul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc (a+i)) 2) (sq_nonneg _)
end PrimeSquares
