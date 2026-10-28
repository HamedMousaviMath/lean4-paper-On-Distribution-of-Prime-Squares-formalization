import PrimeSquares.AnnularBoundaryBounds

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem quadratic_integral_parts {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    quadraticPhaseSlope θ*(∫ t in a..b, quadraticOscillation θ t) =
      annularBoundaryWeight 1 b*quadraticOscillation θ b-
      annularBoundaryWeight 1 a*quadraticOscillation θ a-
      ∫ t in a..b, annularBoundaryDerivative 1 t*quadraticOscillation θ t := by
  have hint : IntervalIntegrable (annularBoundaryDerivative 1) volume a b :=
    (annularBoundaryDerivative_continuousOn 1 ha).intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := annularBoundaryWeight 1) (u' := annularBoundaryDerivative 1)
    (v := quadraticOscillation θ) (v' := quadraticOscillationDerivative θ)
    (by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact annularBoundaryWeight_hasDerivAt 1 (ha.trans_le ht.1))
    (fun t _ => quadraticOscillation_hasDerivAt θ t) hint
    (quadraticOscillationDerivative_intervalIntegrable θ a b)
  have he : (∫ t in a..b, annularBoundaryWeight 1 t*quadraticOscillationDerivative θ t) =
      quadraticPhaseSlope θ*(∫ t in a..b, quadraticOscillation θ t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simpa only [sub_self, Real.rpow_zero, Complex.ofReal_one, one_mul] using
      annularBoundaryWeight_phase_derivative 1 θ (ha.trans_le ht.1)
  rwa [he] at hparts

theorem inverse_square_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, t^(-(2 : ℝ))) = a⁻¹-b⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ => t^(-(2 : ℝ))) (Set.Icc a b) := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (p := -(2 : ℝ))
      (Or.inl (ha.trans_le ht.1).ne')).continuousAt.continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun s : ℝ => -(s^(-(1 : ℝ)))) (t^(-(2 : ℝ))) t := by
    rw [Set.uIcc_of_le hab] at ht
    convert (Real.hasDerivAt_rpow_const (p := -(1 : ℝ))
      (Or.inl (ha.trans_le ht.1).ne')).neg using 1
    norm_num
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hab)
  simpa only [Real.rpow_neg_one, neg_sub_neg] using h

theorem quadratic_integral_remainder_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ‖∫ t in a..b, annularBoundaryDerivative 1 t*quadraticOscillation θ t‖ ≤ a⁻¹ := by
  have hnorm : (∫ t in a..b, ‖annularBoundaryDerivative 1 t*quadraticOscillation θ t‖) =
      a⁻¹-b⁻¹ := by
    rw [←inverse_square_integral ha hab]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change ‖annularBoundaryDerivative 1 t*quadraticOscillation θ t‖ = t^(-(2 : ℝ))
    rw [norm_mul, quadraticOscillation_norm, mul_one,
      annularBoundaryDerivative_norm 1 (ha.le.trans ht.1)]
    norm_num
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t =>
    annularBoundaryDerivative 1 t*quadraticOscillation θ t) hab
  rw [hnorm] at h
  have hb : 0 ≤ b⁻¹ := inv_nonneg.mpr (ha.le.trans hab)
  linarith

theorem quadratic_integral_tail_scaled {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    (4*Real.pi*|θ|)*‖∫ t in a..b, quadraticOscillation θ t‖ ≤ 3*a⁻¹ := by
  have hb : 0 < b := ha.trans_le hab
  have hi : b⁻¹ ≤ a⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le ha hab
  have hboundary : ‖annularBoundaryWeight 1 b*quadraticOscillation θ b-
      annularBoundaryWeight 1 a*quadraticOscillation θ a‖ ≤ 2*a⁻¹ := by
    calc
      _ ≤ ‖annularBoundaryWeight 1 b*quadraticOscillation θ b‖+
          ‖annularBoundaryWeight 1 a*quadraticOscillation θ a‖ := norm_sub_le _ _
      _ = b⁻¹+a⁻¹ := by
        simp only [norm_mul, quadraticOscillation_norm, mul_one,
          annularBoundaryWeight_norm 1 hb.le, annularBoundaryWeight_norm 1 ha.le]
        norm_num [Real.rpow_neg_one]
      _ ≤ _ := by linarith
  calc
    _ = ‖quadraticPhaseSlope θ*(∫ t in a..b, quadraticOscillation θ t)‖ := by
      rw [norm_mul, quadraticPhaseSlope_norm]
    _ = _ := congrArg norm (quadratic_integral_parts ha hab θ)
    _ ≤ ‖annularBoundaryWeight 1 b*quadraticOscillation θ b-
        annularBoundaryWeight 1 a*quadraticOscillation θ a‖+
        ‖∫ t in a..b, annularBoundaryDerivative 1 t*quadraticOscillation θ t‖ := norm_sub_le _ _
    _ ≤ 2*a⁻¹+a⁻¹ := add_le_add hboundary (quadratic_integral_remainder_bound ha hab θ)
    _ = _ := by ring

end PrimeSquares
