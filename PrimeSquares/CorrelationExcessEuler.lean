import PrimeSquares.CorrelationFactorExpansion

open Finset
namespace PrimeSquares

theorem subsetCorrelationExcess_nonneg (S t : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) (ht : t ⊆ S) :
    0 ≤ subsetCorrelationExcess t :=
  prod_nonneg (fun p hp => correlationExcess_nonneg (hS p (ht hp)))

theorem subsetCorrelationExcess_div_product (t : Finset ℕ) :
    subsetCorrelationExcess t/(subsetProduct t : ℝ)=
      ∏ p ∈ t,2/((p : ℝ)*((p : ℝ)-1)) := by
  rw [subsetCorrelationExcess,subsetProduct,Nat.cast_prod,←prod_div_distrib]
  apply prod_congr rfl
  intro p _
  unfold correlationExcess
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem correlation_excess_euler_bound (D : ℕ) :
    (∑ t ∈ (Nat.primesLE D).powerset,subsetCorrelationExcess t/(subsetProduct t : ℝ)) ≤ Real.exp 2 := by
  simp_rw [subsetCorrelationExcess_div_product]
  rw [←prod_one_add]
  have hs := sum_inv_mul_pred_le_one (Nat.primesLE D) D (by
    intro p hp
    exact ⟨(Nat.prime_of_mem_primesLE hp).two_le,(Nat.mem_primesLE.mp hp).1⟩)
  have ht : (∑ p ∈ Nat.primesLE D,2/((p : ℝ)*((p : ℝ)-1))) ≤ 2 := by
    simpa only [mul_sum,mul_one_div,mul_one] using mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  apply (Real.prod_one_add_le_exp_sum _ ?_).trans (Real.exp_le_exp.mpr ht)
  intro p
  by_cases hp : p=0
  · simp [hp]
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp)
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith))

end PrimeSquares
