import PrimeSquares.GeometricErrorRangeEnergy
namespace PrimeSquares
theorem geometricError_finite_energy {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (e : ℕ → ℝ)
    (he : ∀ j,0 ≤ e j) (hn : ∀ j,e j ≤ C*((4 : ℝ)^j*x))
    (hf : ∀ j,((4 : ℝ)^j*x)*e j ≤ C) (J : Finset ℕ) :
    (∑ j ∈ J,(e j)^2) ≤ (34/15 : ℝ)*C^2 := by
  obtain ⟨n,hJ⟩ := J.exists_nat_subset_range
  exact (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun j _ _ => sq_nonneg (e j))).trans
    (geometricError_range_energy hC hx e he hn hf n)
end PrimeSquares
