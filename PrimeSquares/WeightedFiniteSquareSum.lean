import PrimeSquares.AttenuatedRationalCollars

open Finset
namespace PrimeSquares

theorem norm_finset_sum_square_weighted {ι : Type*} (S : Finset ι) (F : ι → ℂ) (B : ι → ℝ)
    (hB : ∀ i ∈ S,0 < B i) :
    ‖∑ i ∈ S,F i‖^2 ≤ (∑ i ∈ S,B i)*(∑ i ∈ S,‖F i‖^2/B i) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun i => ‖F i‖) (f := fun i => ‖F i‖^2/B i) (g := B)
    (fun i hi => div_nonneg (sq_nonneg _) (hB i hi).le) (fun i hi => (hB i hi).le)
    (fun i hi => by rw [div_mul_cancel₀ _ (hB i hi).ne'])
  have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S F) 2
  simpa only [mul_comm] using ht.trans hc

end PrimeSquares
