import PrimeSquares.CorrelationGlobalExpansion
import PrimeSquares.ReciprocalMultiples

open Finset
namespace PrimeSquares

theorem conductorCorrelationProduct_weighted_expansion (D : ℕ) :
    (∑ n ∈ Icc 1 D,conductorCorrelationProduct n/(n : ℝ))=
      ∑ t ∈ (Nat.primesLE D).powerset,subsetCorrelationExcess t*
        ∑ n ∈ (Icc 1 D).filter (fun n => subsetProduct t ∣ n),(n : ℝ)⁻¹ := by
  classical
  have he (n : ℕ) (hn : n ∈ Icc 1 D) : conductorCorrelationProduct n/(n : ℝ)=
      ∑ t ∈ (Nat.primesLE D).powerset,if subsetProduct t ∣ n then subsetCorrelationExcess t*(n : ℝ)⁻¹ else 0 := by
    obtain ⟨hnp,hnD⟩ := mem_Icc.mp hn
    rw [conductorCorrelationProduct_global_expansion (Nat.primesLE D)
      (fun p hp => Nat.prime_of_mem_primesLE hp) (by omega : n ≠ 0) (primeFactors_le_cutoff (by omega) hnD),div_eq_mul_inv,sum_mul]
    apply sum_congr rfl
    intro t _
    split_ifs <;> simp
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

end PrimeSquares
