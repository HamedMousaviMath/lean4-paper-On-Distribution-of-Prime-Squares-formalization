import PrimeSquares.DyadicAbsoluteProfile
import PrimeSquares.DyadicAnnularProjectionProfile

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem annularProjectionError_absolute_profile {N : ℕ} (hN : 2≤N)
    {β : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (θ : ℝ) :
    ‖annularProjectionError N β θ‖≤annularProjectionErrorConstant*
      min ((N : ℝ)^2*|θ|) (((N : ℝ)^2*|θ|)⁻¹) := by
  have h := (annularProjectionError_profile hN hβ0 hβ1 θ).2
  exact two_sided_absolute_profile (by positivity) h.1 h.2

theorem dyadicAnnularProjectionError_absolute_sum {M : ℕ} (hM : 2≤M)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1) (θ : ℝ) (J : ℕ) :
    (∑ j∈range J,‖annularProjectionError ((2 : ℕ)^j*M) (β j) θ‖)≤
      (10/3 : ℝ)*annularProjectionErrorConstant := by
  have hC : 0≤annularProjectionErrorConstant :=
    (annularProjectionError_profile hM (hβ0 0) (hβ1 0) θ).1.le
  calc
    _ ≤ ∑ j∈range J,annularProjectionErrorConstant*
        min ((4 : ℝ)^j*((M : ℝ)^2*|θ|)) (((4 : ℝ)^j*((M : ℝ)^2*|θ|))⁻¹) := by
      apply sum_le_sum
      intro j _
      have h := dyadicAnnularProjectionError_profile hM β hβ0 hβ1 θ j
      exact two_sided_absolute_profile (by positivity) h.1 h.2
    _ = annularProjectionErrorConstant*∑ j∈range J,
        min ((4 : ℝ)^j*((M : ℝ)^2*|θ|)) (((4 : ℝ)^j*((M : ℝ)^2*|θ|))⁻¹) := (mul_sum _ _ _).symm
    _ ≤ annularProjectionErrorConstant*(10/3 : ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_absolute_profile_sum (by positivity) J) hC
    _ = _ := by ring

end PrimeSquares
