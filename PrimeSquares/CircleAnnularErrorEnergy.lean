import PrimeSquares.CircleAnnularErrorLiftValue
import PrimeSquares.CircleAnnularErrorSupport
import PrimeSquares.CircleSourceCutoffWitness
import PrimeSquares.DyadicAnnularProjectionEnergy
open Finset
namespace PrimeSquares
theorem circleAnnularProjectionError_finite_energy {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 1 ≤ s)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (r : ℚ) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖circleAnnularProjectionError ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r θ‖^2) ≤
      (34/15 : ℝ)*annularProjectionErrorConstant^2 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he]
  by_cases hz : circleSourceCutoff s r (ξ : PrimeCircle)=0
  · have hzj (j : ℕ) := circleAnnularProjectionError_cutoff_zero ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) hs r (ξ : PrimeCircle) hz
    simp only [hzj,norm_zero,zero_pow (by norm_num : 2 ≠ 0),sum_const_zero]
    positivity
  · obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
    have hb : ‖Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k))‖ ≤ 1 := by
      have hn : 0 ≤ sourceArcCutoffScale s (ξ-(r : ℝ)+k) := sourceArcCutoff_nonneg _
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
      exact sourceArcCutoff_le_one _
    calc
      _ ≤ ∑ j ∈ J,‖annularProjectionError ((2 : ℕ)^j*M) (β j) (ξ-(r : ℝ)+k)‖^2 := by
        apply sum_le_sum
        intro j _
        rw [circleAnnularProjectionError_eq_lift _ _ _ hs r ξ k hk,norm_mul]
        apply pow_le_pow_left₀ (by positivity) _ 2
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hb
          (norm_nonneg (annularProjectionError ((2 : ℕ)^j*M) (β j) (ξ-(r : ℝ)+k)))
      _ ≤ _ := dyadicAnnularProjectionError_finite_energy hM β hβ0 hβ1 _ J
end PrimeSquares
