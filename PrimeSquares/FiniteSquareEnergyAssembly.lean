import PrimeSquares.WeightedFiniteSquareSum

open Finset
namespace PrimeSquares

theorem finite_square_energy_assemble {ι : Type*} (S : Finset ι) (J : Finset ℕ)
    (F : ℕ → ι → ℂ) (B : ι → ℝ) (hB : ∀ i ∈ S,0 < B i)
    (hE : ∀ i ∈ S,(∑ j ∈ J,‖F j i‖^2) ≤ (B i)^2) :
    (∑ j ∈ J,‖∑ i ∈ S,F j i‖^2) ≤ (∑ i ∈ S,B i)^2 := by
  calc
    _ ≤ ∑ j ∈ J,(∑ i ∈ S,B i)*(∑ i ∈ S,‖F j i‖^2/B i) :=
      sum_le_sum (fun j _ => norm_finset_sum_square_weighted S (F j) B hB)
    _ = (∑ i ∈ S,B i)*(∑ i ∈ S,(∑ j ∈ J,‖F j i‖^2)/B i) := by
      rw [←mul_sum,sum_comm]
      simp only [Finset.sum_div]
    _ ≤ (∑ i ∈ S,B i)*(∑ i ∈ S,B i) := by
      apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun i hi => (hB i hi).le))
      apply sum_le_sum
      intro i hi
      exact (div_le_div_of_nonneg_right (hE i hi) (hB i hi).le).trans_eq (by rw [sq, mul_div_cancel_right₀ _ (hB i hi).ne'])
    _ = _ := (sq _).symm

end PrimeSquares
