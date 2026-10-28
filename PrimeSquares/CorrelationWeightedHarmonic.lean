import PrimeSquares.CorrelationWeightedDoubleSum
import PrimeSquares.CorrelationExcessEuler

open Finset
namespace PrimeSquares

theorem conductorCorrelationProduct_weighted_harmonic (D : ℕ) :
    (∑ n ∈ Icc 1 D,conductorCorrelationProduct n/(n : ℝ)) ≤ Real.exp 2*(harmonic D : ℝ) := by
  rw [conductorCorrelationProduct_weighted_expansion]
  calc
    _ ≤ ∑ t ∈ (Nat.primesLE D).powerset,subsetCorrelationExcess t*
        ((subsetProduct t : ℝ)⁻¹*(harmonic D : ℝ)) := by
      apply sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (reciprocal_multiples_bound (subsetProduct t) D
          (subsetProduct_pos (Nat.primesLE D) t (fun p hp => Nat.prime_of_mem_primesLE hp) (mem_powerset.mp ht)))
        (subsetCorrelationExcess_nonneg (Nat.primesLE D) t (fun p hp => Nat.prime_of_mem_primesLE hp) (mem_powerset.mp ht))
    _ = (∑ t ∈ (Nat.primesLE D).powerset,subsetCorrelationExcess t/(subsetProduct t : ℝ))*(harmonic D : ℝ) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro t _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (correlation_excess_euler_bound D) (by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      apply sum_nonneg
      intro n _
      simp only [Rat.cast_inv,Rat.cast_natCast]
      positivity)

end PrimeSquares
