import PrimeSquares.DyadicDecayShell
import PrimeSquares.GeometricDyadicTail

namespace PrimeSquares

theorem tenth_order_shell_identity (j : ℕ) :
    ((2 : ℝ)^(j*10))⁻¹*(2 : ℝ)^(j+1)=2*(1/512 : ℝ)^j := by
  rw [pow_succ,←mul_assoc,dyadic_shell_normalization j 10 (by norm_num)]
  norm_num only [Nat.reduceSub]
  rw [pow_mul,←inv_pow]
  norm_num [mul_comm]

theorem tenth_order_shell_partial (J : ℕ) :
    (∑ j ∈ Finset.range J, ((2 : ℝ)^(j*10))⁻¹*(2 : ℝ)^(j+1)) ≤ 1024/511 := by
  simp_rw [tenth_order_shell_identity]
  rw [←Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (dyadic_ninth_partial_bound J) (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at h ⊢
  exact h

end PrimeSquares
