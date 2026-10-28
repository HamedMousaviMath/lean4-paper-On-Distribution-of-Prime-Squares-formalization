import PrimeSquares.CorrelationWeightedLog

open Finset
namespace PrimeSquares

theorem conductorCorrelationProduct_weight_nonneg (d : ℕ) : 0 ≤ conductorCorrelationProduct d/(d : ℝ) :=
  div_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (conductorCorrelationProduct_one_le d)) (Nat.cast_nonneg _)

theorem conductorCorrelationProduct_subset_log (S : Finset ℕ) (D : ℕ) (hD : 1 ≤ D)
    (hS : S ⊆ Icc 1 D) :
    (∑ d ∈ S,conductorCorrelationProduct d/(d : ℝ)) ≤ correlationLogConstant*Real.log (2*(D : ℝ)) := by
  exact (sum_le_sum_of_subset_of_nonneg hS (fun d _ _ => conductorCorrelationProduct_weight_nonneg d)).trans
    (conductorCorrelationProduct_weighted_log D hD)

end PrimeSquares
