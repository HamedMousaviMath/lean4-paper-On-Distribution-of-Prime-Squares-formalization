import PrimeSquares.InducedIntegerCorrelation
import PrimeSquares.CorrelationWeightedSubsets

open Finset
namespace PrimeSquares

theorem inducedIntegerCorrelation_weighted_log (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (S : Finset ℕ) (D : ℕ)
    (hD : 1 ≤ D) (hS : S ⊆ Icc 1 D) (x : ℤ) :
    (∑ d ∈ S,‖inducedIntegerCorrelation q₀ χ₀ d x‖/(d : ℝ)) ≤
      conductorMajorant q₀*correlationLogConstant*Real.log (2*(D : ℝ)) := by
  have hB : 0 ≤ conductorMajorant q₀ := (by norm_num : (0 : ℝ) ≤ 1).trans (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  calc
    _ ≤ ∑ d ∈ S,conductorMajorant q₀*(conductorCorrelationProduct d/(d : ℝ)) := by
      apply sum_le_sum
      intro d _
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
        (inducedIntegerCorrelation_bound q₀ d χ₀ hχ x) (Nat.cast_nonneg d)
    _ = conductorMajorant q₀*∑ d ∈ S,conductorCorrelationProduct d/(d : ℝ) := (mul_sum ..).symm
    _ ≤ conductorMajorant q₀*(correlationLogConstant*Real.log (2*(D : ℝ))) :=
      mul_le_mul_of_nonneg_left (conductorCorrelationProduct_subset_log S D hD hS) hB
    _ = _ := by ring

end PrimeSquares
