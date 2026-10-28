import PrimeSquares.GeometricPowerBudget

open Finset
namespace PrimeSquares

theorem rational_high_weighted_sum (Γ : Finset ℚ) (M : ℕ) (ξ : ℝ) (F : ℚ → ℂ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)
    (hzero : ∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F r=0)
    (hF : ∀ r ∈ Γ,‖F r‖ ≤ A*(r.den : ℝ)^(-ε)) :
    ‖∑ r ∈ Γ,F r‖ ≤ 4*A/(1-(2 : ℝ)^(-ε)) := by
  classical
  rw [rational_dyadic_partition Γ M (fun r hr => (hΓ r hr).2) F]
  calc
    _ ≤ ∑ s ∈ range (Nat.log2 M+1),‖∑ r ∈ Γ.filter (fun r => Nat.log2 r.den=s),F r‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ range (Nat.log2 M+1),4*(A*((2 : ℝ)^(-ε))^s) := by
      apply sum_le_sum
      intro s _
      apply dyadic_sparse_sum_bound _ ξ s F (by positivity)
      · intro r hr
        exact (hΓ r (mem_filter.mp hr).1).1
      · intro r hr
        exact (mem_filter.mp hr).2
      · intro r hr hz
        exact hzero r (mem_filter.mp hr).1 hz
      · intro r hr
        exact (hF r (mem_filter.mp hr).1).trans (mul_le_mul_of_nonneg_left
          (dyadic_inverse_rpow r.den_pos (mem_filter.mp hr).2 hε.le) hA)
    _ = 4*A*(∑ s ∈ range (Nat.log2 M+1),((2 : ℝ)^(-ε))^s) := by simp only [mul_assoc,Finset.mul_sum]
    _ ≤ 4*A*(1-(2 : ℝ)^(-ε))⁻¹ := mul_le_mul_of_nonneg_left (geometric_inverse_power_partial hε _) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

end PrimeSquares
