import PrimeSquares.ContinuousAnnularIncrements

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem annularOscillatoryModel_norm_one {N : ℕ} (hN : 1≤N)
    {β : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (θ : ℝ) :
    ‖annularOscillatoryModel N β θ‖≤1 := by
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  have hp : ((N : ℝ)/2)^(β-1)≤(1/2 : ℝ)^(β-1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hhalf : (1/2 : ℝ)^(β-1)≤2 := by
    calc
      _ ≤ (1/2 : ℝ)^(-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 2 := by norm_num
  exact (annularOscillatoryModel_norm_power hN hβ1 θ).trans (by linarith)

theorem continuousAnnularIncrement_one_start {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (θ : ℝ) (J : ℕ) :
    (∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
      annularOscillatoryModel ((2 : ℕ)^j) β θ‖)≤continuousAnnularIncrementConstant+2 := by
  cases J with
  | zero =>
    simp only [range_zero,sum_empty]
    have h := continuousAnnularIncrementConstant_pos
    linarith
  | succ J =>
    have ht : (∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^((j+1)+1)) β θ-
        annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ‖)≤continuousAnnularIncrementConstant := by
      simpa only [pow_succ] using continuousAnnularIncrement_absolute_sum (M := 2) (by norm_num)
        hβ0 hβ1 θ J
    have hfirst : ‖annularOscillatoryModel 2 β θ-annularOscillatoryModel 1 β θ‖≤2 :=
      (norm_sub_le _ _).trans ((add_le_add
        (annularOscillatoryModel_norm_one (by norm_num : 1≤(2 : ℕ)) hβ0.le hβ1 θ)
        (annularOscillatoryModel_norm_one (by norm_num : 1≤(1 : ℕ)) hβ0.le hβ1 θ)).trans_eq (by norm_num))
    rw [sum_range_succ']
    norm_num only [zero_add,pow_zero,pow_one] at ht ⊢
    linarith

theorem continuousAnnularSignedIncrement_one_start {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j∈range J,‖σ j‖≤1) (θ : ℝ) :
    ‖∑ j∈range J,σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
      annularOscillatoryModel ((2 : ℕ)^j) β θ)‖≤continuousAnnularIncrementConstant+2 := by
  calc
    _ ≤ ∑ j∈range J,‖σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
        annularOscillatoryModel ((2 : ℕ)^j) β θ)‖ := norm_sum_le _ _
    _ ≤ ∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)) β θ-
        annularOscillatoryModel ((2 : ℕ)^j) β θ‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hσ j hj) (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := continuousAnnularIncrement_one_start hβ0 hβ1 θ J

end PrimeSquares
