import PrimeSquares.ExceptionalProgressionDensity

/-!
# Uniform size and exact zero frequency for the genuine annular model

The integration interval is the positive real annulus (N/2,N], with the
manuscript's exact normalization 1/N. No distribution theorem is used.
-/

open MeasureTheory

namespace PrimeSquares

theorem annularOscillatoryIntegrand_norm (β θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.ofReal (t^(β-1)) * quadraticOscillation θ t‖ = t^(β-1) := by
  rw [norm_mul, quadraticOscillation_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht _)]

theorem annularPowerDensity_upper {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : β ≤ 1)
    {t : ℝ} (ht : t ∈ Set.Icc ((N : ℝ)/2) N) :
    t^(β-1) ≤ ((N : ℝ)/2)^(β-1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  exact Real.rpow_le_rpow_of_nonpos (by positivity) ht.1 (by linarith)

theorem annularOscillatoryModel_norm_power {N : ℕ} (hN : 1 ≤ N) {β : ℝ}
    (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularOscillatoryModel N β θ‖ ≤ ((N : ℝ)/2)^(β-1) / 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t => Complex.ofReal (t^(β-1)) * quadraticOscillation θ t)
    (C := ((N : ℝ)/2)^(β-1)) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      rw [annularOscillatoryIntegrand_norm β θ (by linarith [ht.1])]
      exact annularPowerDensity_upper hN hβ ⟨ht.1.le, ht.2⟩)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - (N : ℝ)/2)] at hi
  rw [annularOscillatoryModel_interval, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hNp.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * (((N : ℝ)/2)^(β-1) * ((N : ℝ) - (N : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hNp.le)
    _ = _ := by field_simp; ring

theorem annularOscillatoryModel_norm_half {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularOscillatoryModel N β θ‖ ≤ 1/2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ((N : ℝ)/2)^(β-1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  exact (annularOscillatoryModel_norm_power (by omega) hβ θ).trans (by linarith)

theorem annularOscillatoryModel_zero_explicit {N : ℕ} (hN : 1 ≤ N)
    {β : ℝ} (hβ : 0 < β) :
    annularOscillatoryModel N β 0 =
      Complex.ofReal (((N : ℝ)^β - ((N : ℝ)/2)^β) / ((N : ℝ)*β)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => Complex.ofReal (t^(β-1)))
      volume ((N : ℝ)/2) N :=
    (Complex.continuous_ofReal.comp_continuousOn
      (exceptionalDensity_continuousOn β (by positivity))).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t => Complex.ofReal (exceptionalPrimitive β t))
    (f' := fun t => Complex.ofReal (t^(β-1))) (by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact (exceptionalPrimitive_hasDerivAt hβ
        ((by positivity : (0 : ℝ) < (N : ℝ)/2).trans_le ht.1)).ofReal_comp) hint
  rw [annularOscillatoryModel_interval]
  simp only [quadraticOscillation, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [hftc]
  simp only [exceptionalPrimitive, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
  congr 1
  field_simp
