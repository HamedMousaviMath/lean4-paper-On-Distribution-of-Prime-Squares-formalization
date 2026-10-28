import PrimeSquares.TruncatedGaugeStrongPower
import PrimeSquares.NearOneStrongConstant

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
namespace PrimeSquares

theorem finiteInput_enorm_power_sum (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ x, x ∉ F → f x = 0) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x : ℤ, ‖f x‖ₑ^p ∂Measure.count) = ∑ x ∈ F, ENNReal.ofReal (‖f x‖^p) := by
  rw [lintegral_count, tsum_eq_sum (s := F) (fun x hx => by
    rw [hf x hx, enorm_zero, ENNReal.zero_rpow_of_pos hp])]
  apply Finset.sum_congr rfl
  intro x _
  rw [←ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

theorem count_strong_power_to_norm (u : ℤ → ℝ) (hu : ∀ x, 0 ≤ u x) (f : ℤ → ℂ)
    {p B : ℝ} (hp : 1 < p) (hB : 1 ≤ B)
    (hf : MemLp f (ENNReal.ofReal p) Measure.count)
    (H : (∫⁻ x : ℤ, ENNReal.ofReal ((u x)^p) ∂Measure.count) ≤
      ENNReal.ofReal B*(∫⁻ x : ℤ, ‖f x‖ₑ^p ∂Measure.count)) :
    MemLp u (ENNReal.ofReal p) Measure.count ∧
      eLpNorm u (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal B*eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPT : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hm : AEStronglyMeasurable u Measure.count := AEStronglyMeasurable.of_discrete
  have he : (∫⁻ x : ℤ, ‖u x‖ₑ^p ∂Measure.count) =
      ∫⁻ x : ℤ, ENNReal.ofReal ((u x)^p) ∂Measure.count := by
    apply lintegral_congr
    intro x
    rw [←ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hu x),
      ENNReal.ofReal_rpow_of_nonneg (hu x) hp0.le]
  have hfint : (∫⁻ x : ℤ, ‖f x‖ₑ^p ∂Measure.count) < ∞ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hP0 hPT hf.eLpNorm_lt_top
  have hfinite : (∫⁻ x : ℤ, ‖u x‖ₑ^p ∂Measure.count) < ∞ := by
    rw [he]
    exact H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfint)
  have hmu : MemLp u (ENNReal.ofReal p) Measure.count := by
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0 hPT hm).mpr
      (by simpa only [ENNReal.toReal_ofReal hp0.le] using hfinite)
  refine ⟨hmu, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPT hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPT hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, he]
  have hpow : (ENNReal.ofReal B)^(1/p) ≤ ENNReal.ofReal B := by
    have hB' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hB
    exact (ENNReal.rpow_le_rpow_of_exponent_le hB' ((div_le_one hp0).mpr (by linarith))).trans_eq
      (ENNReal.rpow_one _)
  calc
    _ ≤ (ENNReal.ofReal B*(∫⁻ x : ℤ, ‖f x‖ₑ^p ∂Measure.count))^(1/p) :=
      ENNReal.rpow_le_rpow H (by positivity)
    _ = (ENNReal.ofReal B)^(1/p)*(∫⁻ x : ℤ, ‖f x‖ₑ^p ∂Measure.count)^(1/p) :=
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ _ := mul_le_mul_left hpow _

theorem actual_finite_strong_maximal_norm (A : PositiveAverageFamily) {C C₀ K : ℝ}
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (hK : 1 ≤ K)
    (H : ∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
      ∀ t : ℝ, 0 < t → {x | t < positiveMaximal A f x}.Finite ∧
      ({x | t < positiveMaximal A f x}.ncard : ℝ) ≤
        K*∑ x ∈ F.filter (fun x => t/C₀ < ‖f x‖), nearOnePsi C (‖f x‖/t))
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x, x ∉ F → f x = 0)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    MemLp (positiveMaximal A f) (ENNReal.ofReal p) Measure.count ∧
      eLpNorm (positiveMaximal A f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (Real.exp (nearOneStrongConstant C C₀ K/(p-1)*Real.log (Real.exp 1/(p-1))))*
          eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := by linarith
  have hCpos := nearOneStrongConstant_pos hC hC₀ hK
  have hT := (nearOne_log_reciprocal_bounds (by linarith : 0 < p-1) (by linarith : p-1 ≤ 1)).1
  have hrate : 1 ≤ Real.exp (nearOneStrongConstant C C₀ K/(p-1)*Real.log (Real.exp 1/(p-1))) := by
    apply Real.one_le_exp_iff.mpr
    have h := mul_nonneg hCpos.le (show 0 ≤ (1/(p-1))*Real.log (Real.exp 1/(p-1)) by linarith)
    convert h using 1; ring
  have hfLp : MemLp f (ENNReal.ofReal p) Measure.count := by
    have h := finiteInputLp_count_memLp F f (p := ENNReal.ofReal p)
      (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0)
    have he : (finiteInputLp F f 2 : ℤ → ℂ) = f := by
      funext x
      rw [finiteInputLp_apply]
      split_ifs with hx
      · rfl
      · exact (hf x hx).symm
    rwa [he] at h
  apply count_strong_power_to_norm (positiveMaximal A f)
    (positiveMaximal_nonneg A (sum_nonneg (fun x _ => norm_nonneg (f x))) (finiteFunction_norm_bound F f hf))
    f hp hrate hfLp
  have hpow := truncated_gauge_strong_power A hC hC₀ (by linarith : 0 ≤ K) H F f hf hp hp2
  rw [finiteInput_enorm_power_sum F f hf hp0]
  exact hpow.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (nearOneStrong_power_budget hC₀ hK hp hp2)) _)

end PrimeSquares
