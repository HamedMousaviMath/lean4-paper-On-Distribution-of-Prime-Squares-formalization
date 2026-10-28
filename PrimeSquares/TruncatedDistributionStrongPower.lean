import PrimeSquares.TruncatedPowerKernel
import PrimeSquares.IntegerLpMeasureBridge

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped ENNReal
namespace PrimeSquares

theorem truncated_distribution_strong_power (F : Finset ℤ) (a g : ℤ → ℝ)
    (ha : ∀ x ∈ F, 0 ≤ a x) (hg : ∀ x, 0 ≤ g x)
    {K P C₀ p q : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P) (hC₀ : 0 < C₀)
    (hq : 0 < q) (hpq : q < p)
    (H : ∀ t : ℝ, 0 < t →
      Measure.count {x | t < g x} ≤ ENNReal.ofReal (K*P)*
        ∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q) else 0) :
    (∫⁻ x : ℤ, ENNReal.ofReal ((g x)^p) ∂Measure.count) ≤
      ENNReal.ofReal (K*P*p*(C₀^(p-q)/(p-q)))*∑ x ∈ F, ENNReal.ofReal ((a x)^p) := by
  have hp : 0 < p := hq.trans hpq
  have hc : 0 ≤ C₀^(p-q)/(p-q) := by positivity
  rw [nonneg_power_layerCake Measure.count (Filter.Eventually.of_forall hg)
    (AEStronglyMeasurable.of_discrete : AEStronglyMeasurable g Measure.count).aemeasurable hp]
  have hbound : (∫⁻ t in Ioi 0, Measure.count {x | t < g x}*ENNReal.ofReal (p*t^(p-1))) ≤
      ∫⁻ t in Ioi 0, ENNReal.ofReal (K*P*p)*
        ∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q*t^(p-1)) else 0 := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hv : (∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q) else 0)*
        ENNReal.ofReal (t^(p-1)) =
        ∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q*t^(p-1)) else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs
      · rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg (ha x hx) ht0.le) _)]
      · rw [zero_mul]
    calc
      _ ≤ (ENNReal.ofReal (K*P)*(∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q) else 0))*
          ENNReal.ofReal (p*t^(p-1)) := mul_le_mul_left (H t ht0) _
      _ = ENNReal.ofReal (K*P*p)*
          ((∑ x ∈ F, if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q) else 0)*ENNReal.ofReal (t^(p-1))) := by
        rw [ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul (mul_nonneg hK hP)]
        ring
      _ = _ := by rw [hv]
  apply hbound.trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum F (fun x _ => Measurable.ite
      (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const)]
  have hs : (∑ x ∈ F, ∫⁻ t in Ioi 0,
      if t/C₀ < a x then ENNReal.ofReal ((a x/t)^q*t^(p-1)) else 0) =
      ENNReal.ofReal (C₀^(p-q)/(p-q))*∑ x ∈ F, ENNReal.ofReal ((a x)^p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [truncated_scaled_power_kernel (ha x hx) hC₀ hq hpq, ENNReal.ofReal_mul hc]
  rw [hs, ←mul_assoc, ←ENNReal.ofReal_mul (by positivity : 0 ≤ K*P*p)]

end PrimeSquares
