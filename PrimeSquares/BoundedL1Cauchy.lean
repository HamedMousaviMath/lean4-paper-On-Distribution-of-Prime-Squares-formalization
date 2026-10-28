import PrimeSquares.ErgodicL1Operators
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

theorem bounded_L1_cauchy_of_ae_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (v : ℕ → Lp ℂ 1 μ) {B : ℝ}
    (hB : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖v n x‖ ≤ B)
    (hc : ∀ᵐ x ∂μ, CauchySeq (fun n : ℕ => v n x)) : CauchySeq v := by
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun k : ℕ × ℕ => ‖v k.1 x-v k.2 x‖) atTop (𝓝 0) := by
    filter_upwards [hc] with x hx
    apply Metric.tendsto_nhds.mpr
    intro e he
    obtain ⟨J, hJ⟩ := Metric.cauchySeq_iff.mp hx e he
    filter_upwards [eventually_ge_atTop (J,J)] with k hk
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm, dist_eq_norm, sub_zero] using hJ k.1 hk.1 k.2 hk.2
  have hI : Tendsto (fun k : ℕ × ℕ => ∫ x, ‖v k.1 x-v k.2 x‖ ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (f := fun _ : X => (0 : ℝ)) (fun _ : X => 2*B)
      (Filter.Eventually.of_forall (fun k : ℕ × ℕ =>
        ((Lp.aestronglyMeasurable (v k.1)).sub (Lp.aestronglyMeasurable (v k.2))).norm))
      (Filter.Eventually.of_forall (fun k : ℕ × ℕ => by
        filter_upwards [hB k.1, hB k.2] with x hx hy
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith)))
      (integrable_const (2*B)) hlim
    simpa only [integral_zero, Pi.sub_apply] using h
  have hd (n m : ℕ) : dist (v n) (v m) = ∫ x, ‖v n x-v m x‖ ∂μ := by
    rw [Lp.dist_def,
      eLpNorm_one_eq_lintegral_enorm ((Lp.aestronglyMeasurable (v n)).sub (Lp.aestronglyMeasurable (v m)))]
    simpa only [Pi.sub_apply] using
      (integral_norm_eq_lintegral_enorm ((Lp.aestronglyMeasurable (v n)).sub (Lp.aestronglyMeasurable (v m)))).symm
  apply Metric.cauchySeq_iff.mpr
  intro e he
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hI.eventually (gt_mem_nhds he))
  refine ⟨max J.1 J.2, ?_⟩
  intro n hn m hm
  rw [hd]
  exact hJ (n,m) ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hm⟩

end PrimeSquares
