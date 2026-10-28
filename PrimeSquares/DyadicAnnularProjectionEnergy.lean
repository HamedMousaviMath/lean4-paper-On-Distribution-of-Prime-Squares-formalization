import PrimeSquares.DyadicAnnularProjectionProfile
import PrimeSquares.GeometricErrorFiniteEnergy
namespace PrimeSquares
theorem dyadicAnnularProjectionError_finite_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (θ : ℝ) (J : Finset ℕ) :
    (∑ j ∈ J,‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖^2) ≤
      (34/15 : ℝ)*annularProjectionErrorConstant^2 := by
  have hC : 0 ≤ annularProjectionErrorConstant :=
    (annularProjectionError_profile hM (hβ0 0) (hβ1 0) θ).1.le
  exact geometricError_finite_energy hC (by positivity : 0 ≤ (M : ℝ)^2*|θ|)
    (fun j => ‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖) (fun _ => norm_nonneg _)
    (fun j => (dyadicAnnularProjectionError_profile hM β hβ0 hβ1 θ j).1)
    (fun j => (dyadicAnnularProjectionError_profile hM β hβ0 hβ1 θ j).2) J
end PrimeSquares
