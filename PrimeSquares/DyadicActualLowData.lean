import PrimeSquares.DyadicSourceEighthPower

open scoped lp
namespace PrimeSquares

noncomputable def dyadicActualLowData {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 2 ≤ Q)
    (hbudget : ∀ j : ℕ,(sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)^4 ≤ ((((2 : ℕ)^j*M : ℕ) : ℝ))/2)
    (q₀ : ℕ → ℕ) (hq₀ : ∀ j,0 < q₀ j) (χ : ∀ j,DirichletCharacter ℂ (q₀ j)) (hχ : ∀ j,(χ j).IsQuadratic)
    (active : ℕ → Bool) (β : ℕ → ℝ) (hβ : ∀ j,β j ≤ 1) (j : ℕ) :
    NaturalSourceLowData ((2 : ℕ)^j*M) Q where
  scale_lower := dyadic_annular_scale_lower hM j
  cutoff_lower := hQ
  radius := sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q
  cutoff_le := source_cutoff_le_dyadic_radius (by linarith) M j
  scale_budget := hbudget j
  conductor := q₀ j
  conductor_pos := hq₀ j
  character := χ j
  quadratic := hχ j
  active := active j
  beta := β j
  beta_le_one := hβ j

theorem dyadicActualLowData_norm {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 2 ≤ Q)
    (hbudget : ∀ j : ℕ,(sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)^4 ≤ ((((2 : ℕ)^j*M : ℕ) : ℝ))/2)
    (q₀ : ℕ → ℕ) (hq₀ : ∀ j,0 < q₀ j) (χ : ∀ j,DirichletCharacter ℂ (q₀ j)) (hχ : ∀ j,(χ j).IsQuadratic)
    (active : ℕ → Bool) (β : ℕ → ℝ) (hβ : ∀ j,β j ≤ 1) (j : ℕ) :
    ‖fourierL1Operator (dyadicActualLowData hM hQ hbudget q₀ hq₀ χ hχ active β hβ j).symbol‖ ≤
      2*realLowAmplitude M Q := by
  have hMN : M ≤ (2 : ℕ)^j*M := by
    have hp : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right M hp
  exact (naturalSourceLowData_L1_norm _).trans (mul_le_mul_of_nonneg_left
    (realLowAmplitude_scale_mono (by omega) hMN (by linarith)) (by norm_num))

end PrimeSquares
