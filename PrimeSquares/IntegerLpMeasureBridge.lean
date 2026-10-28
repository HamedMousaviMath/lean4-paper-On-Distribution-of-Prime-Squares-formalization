import PrimeSquares.UniformFiniteLpMaximum
import PrimeSquares.FiniteComplexInputs
import PrimeSquares.InitialPositiveDistribution

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal lp
namespace PrimeSquares

theorem memℓp_of_count_memLp {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 0 < p.toReal) {f : ℤ → E} (hf : MemLp f p Measure.count) :
    Memℓp f p := by
  have hp0 : p ≠ 0 := (ENNReal.toReal_pos_iff.mp hp).1.ne'
  have hpT : p ≠ ∞ := (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hInt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpT hf.eLpNorm_lt_top
  rw [lintegral_count] at hInt
  have hs := ENNReal.summable_toReal hInt.ne
  apply memℓp_gen
  simpa only [←ENNReal.toReal_rpow, toReal_enorm] using hs

theorem eLpNorm_count_eq_lp_enorm {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 0 < p.toReal) (f : ℓ^p(ℤ,E)) :
    eLpNorm (f : ℤ → E) p Measure.count = ENNReal.ofReal ‖f‖ := by
  have hp0 : p ≠ 0 := (ENNReal.toReal_pos_iff.mp hp).1.ne'
  have hpT : p ≠ ∞ := (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hs := (lp.memℓp f).summable hp
  have hsum : (∑' x : ℤ, ‖f x‖ₑ^p.toReal) = ENNReal.ofReal (∑' x : ℤ, ‖f x‖^p.toReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _) hs]
    apply tsum_congr
    intro x
    rw [←ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT AEStronglyMeasurable.of_discrete,
    lintegral_count, hsum, ENNReal.ofReal_rpow_of_nonneg
      (tsum_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _)) (by positivity), lp.norm_eq_tsum_rpow hp]

theorem count_memLp_of_memℓp {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 0 < p.toReal) {f : ℤ → E} (hf : Memℓp f p) :
    MemLp f p Measure.count := by
  let F : ℓ^p(ℤ,E) := ⟨f, hf⟩
  change eLpNorm (F : ℤ → E) p Measure.count < ∞
  rw [eLpNorm_count_eq_lp_enorm hp F]
  exact ENNReal.ofReal_lt_top

theorem finiteInputLp_count_memLp (F : Finset ℤ) (f : ℤ → ℂ)
    {p : ℝ≥0∞} (hp : 0 < p.toReal) :
    MemLp (finiteInputLp F f 2 : ℤ → ℂ) p Measure.count := by
  have he : (finiteInputLp F f 2 : ℤ → ℂ) = (finiteInputLp F f p : ℤ → ℂ) := by
    funext x
    rw [finiteInputLp_apply, finiteInputLp_apply]
  rw [he]
  exact count_memLp_of_memℓp hp (lp.memℓp (finiteInputLp F f p))

theorem finiteIndicatorLp_norm_power (F : Finset ℤ) {p : ℝ≥0∞} (hp : 0 < p.toReal) :
    ‖finiteIndicatorLp F p‖^p.toReal = (F.card : ℝ) := by
  rw [←finiteInputLp_one F p, finiteInputLp_norm_rpow F (fun _ => (1 : ℂ)) p hp]
  simp

theorem count_Lp_indicator_power_budget {p : ℝ≥0∞} (hp : 0 < p.toReal)
    {g : ℤ → ℝ} (hg : MemLp g p Measure.count) (hg0 : ∀ x, 0 ≤ g x)
    (F : Finset ℤ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : eLpNorm g p Measure.count ≤
      ENNReal.ofReal K * eLpNorm (finiteIndicatorLp F 2 : ℤ → ℂ) p Measure.count) :
    FinitePowerBudget g p.toReal (K^p.toReal*(F.card : ℝ)) := by
  let G : ℓ^p(ℤ,ℝ) := ⟨g, memℓp_of_count_memLp hp hg⟩
  have hinput : eLpNorm (finiteIndicatorLp F 2 : ℤ → ℂ) p Measure.count =
      ENNReal.ofReal ‖finiteIndicatorLp F p‖ := by
    change eLpNorm (finiteIndicatorLp F p : ℤ → ℂ) p Measure.count = _
    exact eLpNorm_count_eq_lp_enorm hp _
  have houtput : eLpNorm g p Measure.count = ENNReal.ofReal ‖G‖ :=
    eLpNorm_count_eq_lp_enorm hp G
  rw [hinput, houtput, ←ENNReal.ofReal_mul hK] at hbound
  have hnorm : ‖G‖ ≤ K*‖finiteIndicatorLp F p‖ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (lp.norm_nonneg' (finiteIndicatorLp F p)))).mp hbound
  have hpow := Real.rpow_le_rpow (lp.norm_nonneg' G) hnorm hp.le
  rw [Real.mul_rpow hK (lp.norm_nonneg' (finiteIndicatorLp F p)), finiteIndicatorLp_norm_power F hp] at hpow
  intro D
  exact (finitePowerBudget_lp hp G hg0 D).trans hpow

end PrimeSquares
