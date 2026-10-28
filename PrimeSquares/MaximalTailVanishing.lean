import PrimeSquares.MaximalTailMonotonicity

open Filter
open scoped lp Topology
namespace PrimeSquares

theorem operatorMaximalL2_tail_norm_tendsto_zero
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Tendsto (fun J : ℕ => ‖operatorMaximalL2 (fun j => T (J+j))
      (operator_tail_norm_summable T hT J) f‖) atTop (𝓝 0) := by
  have ht := (tendsto_sum_nat_add (fun j : ℕ => ‖T j‖)).mul_const ‖f‖
  have he : Tendsto (fun J : ℕ => (∑' j : ℕ, ‖T (J+j)‖)*‖f‖) atTop (𝓝 0) := by
    simpa only [Nat.add_comm,zero_mul] using ht
  exact squeeze_zero (fun J => norm_nonneg _)
    (fun J => operatorMaximalL2_norm_bound _ (operator_tail_norm_summable T hT J) f) he

theorem operatorMaximalL2_tail_tendsto_zero
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Tendsto (fun J : ℕ => operatorMaximalL2 (fun j => T (J+j))
      (operator_tail_norm_summable T hT J) f) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (operatorMaximalL2_tail_norm_tendsto_zero T hT f)

end PrimeSquares
