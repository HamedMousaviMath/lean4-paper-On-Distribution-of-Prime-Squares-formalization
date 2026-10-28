import PrimeSquares.AnnularMassVariation
import PrimeSquares.AnnularAbsoluteError
import PrimeSquares.SourceCutoffVariation

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def continuousAnnularIncrementConstant : ℝ :=
  1+80/3+(20/3)*annularProjectionErrorConstant

theorem continuousAnnularIncrementConstant_pos : 0<continuousAnnularIncrementConstant := by
  unfold continuousAnnularIncrementConstant annularProjectionErrorConstant
  positivity

theorem annularMass_scaled_variation {M : ℕ} (hM : 2≤M)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) :
    (∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β 0-
      annularOscillatoryModel ((2 : ℕ)^j*M) β 0‖)≤1 := by
  have he (n : ℕ) : (∑ j∈range n,‖annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β 0-
      annularOscillatoryModel ((2 : ℕ)^j*M) β 0‖)=
      (annularOscillatoryModel M β 0).re-(annularOscillatoryModel ((2 : ℕ)^n*M) β 0).re := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,ih,annularMass_difference_norm
        (by have h := dyadic_annular_scale_lower hM n;omega)
        (dyadic_annular_scale_mono (M := M) (by omega : n≤n+1)) hβ0 hβ1]
      ring
  rw [he]
  have h0 := (annularMass_re_bounds (by omega : 1≤M) hβ0 hβ1).2
  have hJ := (annularMass_re_bounds
    (by have h := dyadic_annular_scale_lower hM J;omega : 1≤2^J*M) hβ0 hβ1).1
  linarith

theorem annularIncrement_norm_bound {N M : ℕ} (hN : 2≤N)
    {β : ℝ} (hβ1 : β≤1) (θ : ℝ) :
    ‖annularOscillatoryModel M β θ-annularOscillatoryModel N β θ‖≤
      ‖annularOscillatoryModel M β 0-annularOscillatoryModel N β 0‖+
      |sourceArcCutoff ((M : ℝ)^2*θ)-sourceArcCutoff ((N : ℝ)^2*θ)|+
      ‖annularProjectionError M β θ‖+‖annularProjectionError N β θ‖ := by
  let A := (annularOscillatoryModel M β 0-annularOscillatoryModel N β 0)*
    Complex.ofReal (sourceArcCutoff ((M : ℝ)^2*θ))
  let B := annularOscillatoryModel N β 0*
    Complex.ofReal (sourceArcCutoff ((M : ℝ)^2*θ)-sourceArcCutoff ((N : ℝ)^2*θ))
  have he : annularOscillatoryModel M β θ-annularOscillatoryModel N β θ=
      (A+B)+annularProjectionError M β θ-annularProjectionError N β θ := by
    dsimp [A,B,annularProjectionError]
    push_cast
    ring
  have hA : ‖A‖≤‖annularOscillatoryModel M β 0-annularOscillatoryModel N β 0‖ := by
    dsimp [A]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans_eq (mul_one _)
  have hB : ‖B‖≤|sourceArcCutoff ((M : ℝ)^2*θ)-sourceArcCutoff ((N : ℝ)^2*θ)| := by
    dsimp [B]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hm : ‖annularOscillatoryModel N β 0‖≤1 :=
      (annularOscillatoryModel_norm_half hN hβ1 0).trans (by norm_num)
    exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans_eq (one_mul _)
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le A B).trans (add_le_add hA hB)) le_rfl)) le_rfl)

theorem continuousAnnularIncrement_absolute_sum {M : ℕ} (hM : 2≤M)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (θ : ℝ) (J : ℕ) :
    (∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β θ-
      annularOscillatoryModel ((2 : ℕ)^j*M) β θ‖)≤continuousAnnularIncrementConstant := by
  have hm := annularMass_scaled_variation hM hβ0 hβ1 J
  have hc : (∑ j∈range J,|sourceArcCutoff ((((2 : ℕ)^(j+1)*M : ℕ) : ℝ)^2*θ)-
      sourceArcCutoff ((((2 : ℕ)^j*M : ℕ) : ℝ)^2*θ)|)≤80/3 := by
    simpa only [dyadic_square_scale,mul_assoc] using sourceCutoff_dyadic_variation ((M : ℝ)^2*θ) J
  have he0 := dyadicAnnularProjectionError_absolute_sum hM (fun _ => β)
    (fun _ => hβ0.le) (fun _ => hβ1) θ J
  have h2M : 2≤2*M := by omega
  have hscale (j : ℕ) : (2 : ℕ)^(j+1)*M=(2 : ℕ)^j*(2*M) := by rw [pow_succ];ring
  have he1 : (∑ j∈range J,‖annularProjectionError ((2 : ℕ)^(j+1)*M) β θ‖)≤
      (10/3 : ℝ)*annularProjectionErrorConstant := by
    simpa only [hscale] using dyadicAnnularProjectionError_absolute_sum h2M (fun _ => β)
      (fun _ => hβ0.le) (fun _ => hβ1) θ J
  have hs := sum_le_sum (s := range J) (fun j _ => annularIncrement_norm_bound (M := (2 : ℕ)^(j+1)*M)
    (dyadic_annular_scale_lower hM j) hβ1 θ)
  simp only [sum_add_distrib] at hs
  unfold continuousAnnularIncrementConstant
  linarith

theorem continuousAnnularSignedIncrement_bound {M : ℕ} (hM : 2≤M)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ → ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) (θ : ℝ) :
    ‖∑ j∈range J,σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β θ-
      annularOscillatoryModel ((2 : ℕ)^j*M) β θ)‖≤continuousAnnularIncrementConstant := by
  calc
    _ ≤ ∑ j∈range J,‖σ j*(annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β θ-
        annularOscillatoryModel ((2 : ℕ)^j*M) β θ)‖ := norm_sum_le _ _
    _ ≤ ∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)*M) β θ-
        annularOscillatoryModel ((2 : ℕ)^j*M) β θ‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hσ j hj) (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := continuousAnnularIncrement_absolute_sum hM hβ0 hβ1 θ J

end PrimeSquares
