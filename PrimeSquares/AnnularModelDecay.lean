import PrimeSquares.AnnularBoundaryBounds
import PrimeSquares.AnnularModelSize

/-!
# Uniform frequency decay of the actual normalized annular models
-/

namespace PrimeSquares

theorem annularOscillatoryModel_scaled_decay {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    (4 * Real.pi * |θ|) * ‖annularOscillatoryModel N β θ‖ ≤ 8 / (N : ℝ)^2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  have hraw :
      (4 * Real.pi * |θ|) *
        ‖∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t‖ ≤
      8 / (N : ℝ) := by
    calc
      _ = ‖quadraticPhaseSlope θ *
          (∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t)‖ := by
        rw [norm_mul, quadraticPhaseSlope_norm]
      _ = _ := congrArg norm (annularOscillatory_integrationByParts (by omega) β θ)
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 4 / (N : ℝ) + 4 / (N : ℝ) :=
        add_le_add (annularOscillatory_boundary_norm hN hβ1 θ)
          (annularOscillatory_remainder_norm hN hβ0 hβ1 θ)
      _ = _ := by ring
  have hmodel : ‖annularOscillatoryModel N β θ‖ = (N : ℝ)⁻¹ *
      ‖∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t‖ := by
    rw [annularOscillatoryModel_interval, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hNp.le)]
  rw [hmodel]
  calc
    _ = (N : ℝ)⁻¹ * ((4 * Real.pi * |θ|) *
        ‖∫ t in (N : ℝ)/2..N, Complex.ofReal (t^(β-1)) * quadraticOscillation θ t‖) := by ring
    _ ≤ (N : ℝ)⁻¹ * (8 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hNp.le)
    _ = _ := by field_simp

theorem annularOscillatoryModel_decay {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {θ : ℝ} (hθ : θ ≠ 0) :
    ‖annularOscillatoryModel N β θ‖ ≤ 2 / (Real.pi * |θ| * (N : ℝ)^2) := by
  have hK : 0 < 4 * Real.pi * |θ| := by positivity
  calc
    _ ≤ (8 / (N : ℝ)^2) / (4 * Real.pi * |θ|) := by
      apply (le_div_iff₀ hK).mpr
      simpa only [mul_comm] using annularOscillatoryModel_scaled_decay hN hβ0 hβ1 θ
    _ = _ := by field_simp; ring

theorem annularOscillatoryModel_frequency_mass {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ((N : ℝ)^2 * |θ|) * ‖annularOscillatoryModel N β θ‖ ≤ 2 / Real.pi := by
  by_cases hz : θ = 0
  · simp only [hz, abs_zero, mul_zero, zero_mul]
    positivity
  · have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
    have hden : 0 < Real.pi * |θ| * (N : ℝ)^2 := by positivity
    have h := (le_div_iff₀ hden).mp (annularOscillatoryModel_decay hN hβ0 hβ1 hz)
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith only [h]

theorem annularOscillatoryModel_profile {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ‖annularOscillatoryModel N β θ‖ ≤
      (1/2 + 2/Real.pi) / (1 + (N : ℝ)^2 * |θ|) := by
  have hden : 0 < 1 + (N : ℝ)^2 * |θ| := by positivity
  apply (le_div_iff₀ hden).mpr
  have hmass := annularOscillatoryModel_frequency_mass hN hβ0 hβ1 θ
  have hsize := annularOscillatoryModel_norm_half hN hβ1 θ
  nlinarith only [hmass, hsize]

theorem annularOscillatoryModel_outside_arc {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {q R θ : ℝ} (hq : 0 < q) (hR : 0 < R)
    (hθ : R / (q * (N : ℝ)^2) ≤ |θ|) :
    ‖annularOscillatoryModel N β θ‖ ≤ 2 * q / (Real.pi * R) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  have hden : 0 < q * (N : ℝ)^2 := by positivity
  have hr := (div_le_iff₀ hden).mp hθ
  have hu : R / q ≤ (N : ℝ)^2 * |θ| := by
    apply (div_le_iff₀ hq).mpr
    nlinarith only [hr]
  have hm := (mul_le_mul_of_nonneg_right hu
    (norm_nonneg (annularOscillatoryModel N β θ))).trans
      (annularOscillatoryModel_frequency_mass hN hβ0 hβ1 θ)
  have hs := mul_le_mul_of_nonneg_left hm hq.le
  have he : q * (R / q * ‖annularOscillatoryModel N β θ‖) =
      R * ‖annularOscillatoryModel N β θ‖ := by field_simp
  rw [he] at hs
  apply (le_div_iff₀ (mul_pos Real.pi_pos hR)).mpr
  have ht := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  have hp : Real.pi * (q * (2 / Real.pi)) = 2 * q := by field_simp
  rw [hp] at ht
  nlinarith only [ht]

end PrimeSquares
