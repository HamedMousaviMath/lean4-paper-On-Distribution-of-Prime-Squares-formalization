import PrimeSquares.RealCutoffDyadicBudget

open Finset
namespace PrimeSquares

theorem cutoff_growing_series {Q δ : ℝ} (hQ : 1 ≤ Q) (hδ : δ < 1) :
    (∑ s ∈ range (Nat.log2 ⌊Q⌋₊+1),((2 : ℝ)^(1-δ))^s) ≤
      ((2 : ℝ)^(1-δ)/((2 : ℝ)^(1-δ)-1))*Q^(1-δ) := by
  have hr := collar_dyadic_ratio_gt_one hδ
  calc
    _ ≤ ((2 : ℝ)^(1-δ))^(Nat.log2 ⌊Q⌋₊+1)/((2 : ℝ)^(1-δ)-1) := growing_geometric_partial hr _
    _ = ((2 : ℝ)^(1-δ)/((2 : ℝ)^(1-δ)-1))*((2 : ℝ)^(1-δ))^(Nat.log2 ⌊Q⌋₊) := by rw [pow_succ];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (real_cutoff_growing_power hQ hδ.le) (by positivity)

end PrimeSquares
