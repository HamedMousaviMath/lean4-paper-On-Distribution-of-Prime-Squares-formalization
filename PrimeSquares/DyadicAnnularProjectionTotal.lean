import PrimeSquares.DyadicAnnularProjectionEnergy
namespace PrimeSquares
theorem dyadicAnnularProjectionError_summable {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (θ : ℝ) :
    Summable (fun j => ‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _)
    (dyadicAnnularProjectionError_finite_energy hM β hβ0 hβ1 θ)
theorem dyadicAnnularProjectionError_total {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (θ : ℝ) :
    (∑' j : ℕ,‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖^2) ≤
      (34/15 : ℝ)*annularProjectionErrorConstant^2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    (dyadicAnnularProjectionError_finite_energy hM β hβ0 hβ1 θ)
end PrimeSquares
