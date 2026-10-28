import PrimeSquares.GeometricErrorFiniteEnergy
namespace PrimeSquares
theorem geometricError_square_summable {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (e : ℕ → ℝ)
    (he : ∀ j,0 ≤ e j) (hn : ∀ j,e j ≤ C*((4 : ℝ)^j*x))
    (hf : ∀ j,((4 : ℝ)^j*x)*e j ≤ C) : Summable (fun j => (e j)^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (geometricError_finite_energy hC hx e he hn hf)
theorem geometricError_square_total {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (e : ℕ → ℝ)
    (he : ∀ j,0 ≤ e j) (hn : ∀ j,e j ≤ C*((4 : ℝ)^j*x))
    (hf : ∀ j,((4 : ℝ)^j*x)*e j ≤ C) :
    (∑' j : ℕ,(e j)^2) ≤ (34/15 : ℝ)*C^2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (geometricError_finite_energy hC hx e he hn hf)
end PrimeSquares
