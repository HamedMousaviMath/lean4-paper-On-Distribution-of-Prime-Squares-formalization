import PrimeSquares.FiniteDecayConvolution

open Finset
namespace PrimeSquares

theorem weighted_kernel_sum_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ) (K : ι → ℂ)
    (w : ι → ℝ) (B : ℝ) (hK : ∀ i ∈ S,‖K i‖ ≤ B*w i) :
    ‖∑ i ∈ S,c i*K i‖ ≤ B*∑ i ∈ S,‖c i‖*w i := by
  calc
    _ ≤ ∑ i ∈ S,‖c i*K i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S,B*(‖c i‖*w i) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul]
      have h := mul_le_mul_of_nonneg_left (hK i hi) (norm_nonneg (c i))
      simpa only [mul_comm,mul_left_comm,mul_assoc] using h
    _ = _ := (mul_sum ..).symm

theorem weighted_kernel_sum_majorant {ι : Type*} (S : Finset ι) (K : ι → ℂ)
    (w : ι → ℝ) (B : ℝ) (hK : ∀ i ∈ S,‖K i‖ ≤ B*w i) :
    ‖∑ i ∈ S,K i‖ ≤ B*∑ i ∈ S,w i := by
  simpa only [one_mul,norm_one] using weighted_kernel_sum_bound S (fun _ => (1 : ℂ)) K w B hK

end PrimeSquares
