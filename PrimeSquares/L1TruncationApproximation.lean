import PrimeSquares.OrliczTruncation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

theorem boundedTruncation_norm_le_original {X : Type*} (f : X → ℂ) (m : ℕ) (x : X) :
    ‖boundedTruncation f m x‖ ≤ ‖f x‖ := by
  unfold boundedTruncation
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f x)

theorem boundedTruncation_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hm : Measurable f) (hf : Integrable f μ) (m : ℕ) : Integrable (boundedTruncation f m) μ :=
  hf.norm.mono' (boundedTruncation_measurable hm m).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => boundedTruncation_norm_le_original f m x))

theorem boundedTruncation_L1_tail {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hm : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun m : ℕ => eLpNorm (f-boundedTruncation f m) 1 μ) atTop (𝓝 0) := by
  have hfin : (∫⁻ x, ‖f x‖ₑ ∂μ) ≠ ∞ := ne_of_lt ((hasFiniteIntegral_iff_enorm).mp hf.2)
  have h := tendsto_lintegral_of_dominated_convergence (fun x => ‖f x‖ₑ)
    (fun m => (hm.sub (boundedTruncation_measurable hm m)).enorm)
    (fun m => Filter.Eventually.of_forall (fun x => by
      change ‖(f-boundedTruncation f m) x‖ₑ ≤ ‖f x‖ₑ
      rw [←ofReal_norm, ←ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (boundedTruncation_tail_norm_le f m x))) hfin
    (Filter.Eventually.of_forall (fun x => by
      have ht := continuous_enorm.continuousAt.tendsto.comp (boundedTruncation_tail_tendsto f x)
      simpa only [Function.comp_def, enorm_zero] using ht))
  have he : (fun m : ℕ => eLpNorm (f-boundedTruncation f m) 1 μ) =
      (fun m : ℕ => ∫⁻ x, ‖(f-boundedTruncation f m) x‖ₑ ∂μ) := by
    funext m
    exact eLpNorm_one_eq_lintegral_enorm (hm.sub (boundedTruncation_measurable hm m)).aestronglyMeasurable
  rw [he]
  simpa only [lintegral_zero] using h

theorem L1_bounded_truncation_approximation {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hm : Measurable f) (hf : Integrable f μ) :
    ∃ v : ℕ → Lp ℂ 1 μ,
      (∀ m : ℕ, (v m : X → ℂ) =ᵐ[μ] boundedTruncation f m) ∧
      Tendsto v atTop (𝓝 ((memLp_one_iff_integrable.mpr hf).toLp f)) := by
  let v := fun m : ℕ => (memLp_one_iff_integrable.mpr (boundedTruncation_integrable hm hf m)).toLp (boundedTruncation f m)
  refine ⟨v, fun m => MemLp.coeFn_toLp _, ?_⟩
  have ht : Tendsto (fun m : ℕ => (eLpNorm (f-boundedTruncation f m) 1 μ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (boundedTruncation_L1_tail hm hf)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  apply Metric.tendsto_nhds.mpr
  intro e he
  filter_upwards [ht.eventually (gt_mem_nhds he)] with m hm
  change dist (v m) ((memLp_one_iff_integrable.mpr hf).toLp f) < e
  rw [dist_comm, Lp.dist_edist]
  dsimp only [v]
  rw [Lp.edist_toLp_toLp]
  exact hm

end PrimeSquares
