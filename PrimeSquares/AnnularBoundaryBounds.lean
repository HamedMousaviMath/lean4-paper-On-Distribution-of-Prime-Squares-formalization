import PrimeSquares.AnnularModelIntegrationByParts

/-!
# Bounds for the actual boundary and remainder in quadratic integration by parts
-/

namespace PrimeSquares

theorem quadraticPhaseSlope_norm (θ : ℝ) :
    ‖quadraticPhaseSlope θ‖ = 4 * Real.pi * |θ| := by
  simp only [quadraticPhaseSlope, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.pi_pos]
  norm_num

theorem annularBoundaryWeight_norm (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖annularBoundaryWeight β t‖ = t^(β-2) := by
  rw [annularBoundaryWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht _)]

theorem annularBoundaryDerivative_norm (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖annularBoundaryDerivative β t‖ = |β-2| * t^(β-3) := by
  rw [annularBoundaryDerivative, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht _)]

theorem annularBoundaryWeight_bound {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : β ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc ((N : ℝ)/2) N) :
    ‖annularBoundaryWeight β t‖ ≤ 2 / (N : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : 1 ≤ t := by linarith [ht.1]
  have ha : (0 : ℝ) < (N : ℝ)/2 := by linarith
  rw [annularBoundaryWeight_norm β (by linarith)]
  calc
    t^(β-2) ≤ t^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    _ = t⁻¹ := Real.rpow_neg_one t
    _ ≤ ((N : ℝ)/2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le ha ht.1
    _ = _ := by field_simp

theorem annularBoundaryDerivative_bound {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {t : ℝ} (ht : t ∈ Set.Icc ((N : ℝ)/2) N) :
    ‖annularBoundaryDerivative β t‖ ≤ 8 / (N : ℝ)^2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : 1 ≤ t := by linarith [ht.1]
  have ha : (0 : ℝ) < (N : ℝ)/2 := by linarith
  have hb : |β-2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hp : t^(β-3) ≤ ((N : ℝ)/2)^(-2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : β-3 ≤ -2)).trans
      (Real.rpow_le_rpow_of_nonpos ha ht.1 (by norm_num))
  rw [annularBoundaryDerivative_norm β (by linarith)]
  calc
    |β-2| * t^(β-3) ≤ 2 * ((N : ℝ)/2)^(-2 : ℝ) :=
      mul_le_mul hb hp (Real.rpow_nonneg (by linarith) _) (by norm_num)
    _ = 8 / (N : ℝ)^2 := by
      rw [Real.rpow_neg ha.le, Real.rpow_two]
      field_simp
      ring

theorem annularOscillatory_boundary_norm {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularBoundaryWeight β N * quadraticOscillation θ N -
      annularBoundaryWeight β ((N : ℝ)/2) * quadraticOscillation θ ((N : ℝ)/2)‖ ≤
      4 / (N : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  calc
    _ ≤ ‖annularBoundaryWeight β N * quadraticOscillation θ N‖ +
        ‖annularBoundaryWeight β ((N : ℝ)/2) * quadraticOscillation θ ((N : ℝ)/2)‖ :=
      norm_sub_le _ _
    _ = ‖annularBoundaryWeight β N‖ + ‖annularBoundaryWeight β ((N : ℝ)/2)‖ := by
      simp only [norm_mul, quadraticOscillation_norm, mul_one]
    _ ≤ 2 / (N : ℝ) + 2 / (N : ℝ) :=
      add_le_add (annularBoundaryWeight_bound hN hβ ⟨hab, le_rfl⟩)
        (annularBoundaryWeight_bound hN hβ ⟨le_rfl, hab⟩)
    _ = _ := by ring

theorem annularOscillatory_remainder_norm {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ‖∫ t in (N : ℝ)/2..N, annularBoundaryDerivative β t * quadraticOscillation θ t‖ ≤
      4 / (N : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t => annularBoundaryDerivative β t * quadraticOscillation θ t)
    (C := 8 / (N : ℝ)^2) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      rw [norm_mul, quadraticOscillation_norm, mul_one]
      exact annularBoundaryDerivative_bound hN hβ0 hβ1 ⟨ht.1.le, ht.2⟩)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - (N : ℝ)/2)] at h
  calc
    _ ≤ (8 / (N : ℝ)^2) * ((N : ℝ) - (N : ℝ)/2) := h
    _ = _ := by field_simp; ring

end PrimeSquares
