import PrimeSquares.PositivePowerLayerCake

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace PrimeSquares

theorem truncated_rpow_kernel {b d : ℝ} (hb : 0 ≤ b) (hd : 0 < d) :
    (∫⁻ t in Ioi 0, if t < b then ENNReal.ofReal (t^(d-1)) else 0) =
      ENNReal.ofReal (b^d/d) := by
  have hi : IntegrableOn (fun t : ℝ => t^(d-1)) (Ioo 0 b) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < d-1))).mono_set Ioo_subset_Ioc_self
  have he : (∫ t : ℝ in Ioo 0 b, t^(d-1)) = b^d/d := by
    rw [←integral_Ioc_eq_integral_Ioo, ←intervalIntegral.integral_of_le hb,
      integral_rpow (Or.inl (by linarith : -1 < d-1)), sub_add_cancel, Real.zero_rpow hd.ne', sub_zero]
  calc
    _ = ∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^(d-1)) := by
      change (∫⁻ t in Ioi 0, (Iio b).indicator (fun t : ℝ => ENNReal.ofReal (t^(d-1))) t) = _
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        inter_comm (Iio b) (Ioi 0), Ioi_inter_Iio]
    _ = ENNReal.ofReal (∫ t : ℝ in Ioo 0 b, t^(d-1)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _
    _ = _ := by rw [he]

theorem truncated_scaled_power_kernel {a C₀ p q : ℝ} (ha : 0 ≤ a) (hC₀ : 0 < C₀)
    (hq : 0 < q) (hpq : q < p) :
    (∫⁻ t in Ioi 0, if t/C₀ < a then
      ENNReal.ofReal ((a/t)^q*t^(p-1)) else 0) =
      ENNReal.ofReal (C₀^(p-q)/(p-q)*a^p) := by
  have hd : 0 < p-q := by linarith
  have hb : 0 ≤ C₀*a := mul_nonneg hC₀.le ha
  have hint : (∫⁻ t in Ioi 0, if t/C₀ < a then
      ENNReal.ofReal ((a/t)^q*t^(p-1)) else 0) =
      ENNReal.ofReal (a^q)*(∫⁻ t in Ioi 0, if t < C₀*a then ENNReal.ofReal (t^((p-q)-1)) else 0) := by
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    simp only [div_lt_iff₀ hC₀, mul_comm a C₀]
    split_ifs
    · rw [Real.div_rpow ha ht0.le, div_eq_mul_inv, ←Real.rpow_neg ht0.le,
        mul_assoc, ←Real.rpow_add ht0]
      rw [←ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
      congr 2
      ring_nf
    · rw [mul_zero]
  rw [hint, truncated_rpow_kernel hb hd,
    ←ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
  congr 1
  by_cases ha0 : a = 0
  · subst a
    simp only [Real.zero_rpow hq.ne', Real.zero_rpow (show p ≠ 0 by linarith), mul_zero, zero_mul]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [Real.mul_rpow hC₀.le ha]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      a^q*(C₀^(p-q)*a^(p-q)*(p-q)⁻¹) = C₀^(p-q)*(p-q)⁻¹*(a^q*a^(p-q)) := by ring_nf
      _ = _ := by rw [←Real.rpow_add hap, add_sub_cancel]

end PrimeSquares
