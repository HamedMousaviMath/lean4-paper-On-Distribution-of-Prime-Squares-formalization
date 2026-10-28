import PrimeSquares.RationalProjectionErrorActiveCenter
import PrimeSquares.WeightedCircleAnnularErrorEnergy
open Finset
namespace PrimeSquares
theorem rationalProjectionErrorBlock_finite_energy {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) {A : ℝ} (_hA : 0 ≤ A) (hb : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ A)
    (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖rationalProjectionErrorBlock Γ ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) (c j) θ‖^2) ≤
      A^2*((34/15 : ℝ)*annularProjectionErrorConstant^2) := by
  classical
  by_cases hz : ∀ r ∈ Γ,circleSourceCutoff s r θ=0
  · have he (j : ℕ) := rationalProjectionErrorBlock_zero Γ ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (by omega : 1 ≤ s) (β j) (c j) θ hz
    simp only [he,norm_zero,zero_pow (by norm_num : 2 ≠ 0),sum_const_zero]
    positivity
  · push Not at hz
    obtain ⟨r,hr,hz⟩ := hz
    have he (j : ℕ) := rationalProjectionErrorBlock_active Γ hs hc hd hr θ hz ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (c j)
    simp only [he]
    exact circleAnnularProjectionError_weighted_energy hM (by omega) (fun j => β j r)
      (fun j => hβ0 j r hr) (fun j => hβ1 j r hr) r (fun j => c j r) (fun j => hb j r hr) J θ
end PrimeSquares
