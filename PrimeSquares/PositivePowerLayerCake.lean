import PrimeSquares.NearOneMomentExponential
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace PrimeSquares

theorem positivePower_primitive {p s : ℝ} (hp : 0 < p) :
    (∫ t in 0..s, p*t^(p-1)) = s^p := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < p-1))]
  rw [sub_add_cancel, Real.zero_rpow hp.ne', sub_zero]
  field_simp

theorem nonneg_power_layerCake {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hm : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | t < f x}*ENNReal.ofReal (p*t^(p-1)) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ hf hm
    (fun _ _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p-1)).const_mul p)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hp.le (Real.rpow_nonneg ht.le _))
  simpa only [positivePower_primitive hp] using h

end PrimeSquares
