import PrimeSquares.CircleAnnularErrorEnergy
import PrimeSquares.CircleEnergyMaximalWitness
open scoped lp
namespace PrimeSquares
noncomputable def annularProjectionErrorL2Constant : ℝ := Real.sqrt (34/15)*annularProjectionErrorConstant
theorem annularProjectionErrorL2Constant_pos : 0 < annularProjectionErrorL2Constant := by
  unfold annularProjectionErrorL2Constant annularProjectionErrorConstant
  positivity
theorem annularProjectionErrorL2Constant_sq : annularProjectionErrorL2Constant^2=
    (34/15 : ℝ)*annularProjectionErrorConstant^2 := by
  rw [annularProjectionErrorL2Constant,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 34/15)]
theorem circleAnnularProjectionError_maximum {M : ℕ} (hM : 2 ≤ M) {s : ℕ} (hs : 1 ≤ s)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) (r : ℚ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (circleAnnularProjectionError ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r) f x‖ ≤ g x) ∧
      ‖g‖ ≤ annularProjectionErrorL2Constant*‖f‖ := by
  obtain ⟨g,_,hg,ht,hn⟩ := circle_energy_maximal_witness
    (fun j => circleAnnularProjectionError ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r)
    annularProjectionErrorL2Constant_pos.le (fun J θ => by
      rw [annularProjectionErrorL2Constant_sq]
      exact circleAnnularProjectionError_finite_energy hM hs β hβ0 hβ1 r J θ) f
  exact ⟨g,hg,ht,hn⟩
end PrimeSquares
