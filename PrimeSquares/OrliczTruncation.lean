import PrimeSquares.ErgodicModularMaximal
import PrimeSquares.PrimeMangoldtMaximalComparison
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

noncomputable def boundedTruncation {X : Type*} (f : X → ℂ) (m : ℕ) (x : X) : ℂ :=
  if ‖f x‖ ≤ (m : ℝ) then f x else 0

@[fun_prop]
theorem boundedTruncation_measurable {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : Measurable f) (m : ℕ) : Measurable (boundedTruncation f m) :=
  hf.ite (measurableSet_le hf.norm measurable_const) measurable_const

theorem boundedTruncation_norm_le {X : Type*} (f : X → ℂ) (m : ℕ) (x : X) :
    ‖boundedTruncation f m x‖ ≤ (m : ℝ) := by
  unfold boundedTruncation
  split_ifs with h
  · exact h
  · simp only [norm_zero]
    positivity

theorem boundedTruncation_tail_norm_le {X : Type*} (f : X → ℂ) (m : ℕ) (x : X) :
    ‖(f-boundedTruncation f m) x‖ ≤ ‖f x‖ := by
  unfold boundedTruncation
  simp only [Pi.sub_apply]
  split_ifs
  · simp
  · simp

theorem boundedTruncation_tail_tendsto {X : Type*} (f : X → ℂ) (x : X) :
    Tendsto (fun m : ℕ => (f-boundedTruncation f m) x) atTop (𝓝 0) := by
  have he : (fun m : ℕ => (f-boundedTruncation f m) x) =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
    filter_upwards [eventually_ge_atTop ⌈‖f x‖⌉₊] with m hm
    have hn : ‖f x‖ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
    simp only [Pi.sub_apply, boundedTruncation, ite_eq_left hn, sub_self]
  exact tendsto_const_nhds.congr' he.symm

def NearOneOrliczMember {X : Type*} [MeasurableSpace X] (C : ℝ) (μ : Measure X) (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ a : ℝ, 0 < a ∧ Integrable (fun x => nearOnePsi C (‖f x‖/a)) μ

theorem nearOneOrliczMember_iff {X : Type*} [MeasurableSpace X] {C : ℝ} {μ : Measure X} {f : X → ℂ} :
    NearOneOrliczMember C μ f ↔
      Measurable f ∧ ∃ a : ℝ, 0 < a ∧ (∫⁻ x, ENNReal.ofReal (nearOnePsi C (‖f x‖/a)) ∂μ) < ∞ := by
  constructor
  · rintro ⟨hf, a, ha, hi⟩
    refine ⟨hf, a, ha, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => nearOnePsi_nonneg C (div_nonneg (norm_nonneg _) ha.le)))).mp hi.2
  · rintro ⟨hf, a, ha, hi⟩
    refine ⟨hf, a, ha, ?_⟩
    refine ⟨((nearOnePsi_continuous C).measurable.comp (hf.norm.div_const a)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => nearOnePsi_nonneg C (div_nonneg (norm_nonneg _) ha.le)))).mpr hi

theorem nearOnePsi_change_scale {C a t : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (ht : 0 < t) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 0 ≤ s → nearOnePsi C (s/t) ≤ K*nearOnePsi C (s/a) := by
  let b := max 1 (a/t)
  have hb : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := by linarith
  let K := b*Real.exp (2*C*Real.log b)*(2*Real.exp (2*C*Real.log 2))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s hs
  have hle : s/t ≤ b*(s/a) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 (a/t)) (div_nonneg hs ha.le)
    have he : (a/t)*(s/a) = s/t := by field_simp
    rwa [he] at h
  exact (nearOnePsi_mono C hle).trans (nearOnePsi_rescale_bound hC hb (div_nonneg hs ha.le))

theorem nearOneOrliczMember_integrable {X : Type*} [MeasurableSpace X] {C : ℝ} {μ : Measure X} {f : X → ℂ}
    (hf : NearOneOrliczMember C μ f) (hC : 0 ≤ C) : Integrable f μ := by
  obtain ⟨hm, a, ha, hΨ⟩ := hf
  apply (hΨ.const_mul a).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have h := (div_le_iff₀ ha).mp (nearOnePsi_ge_self hC (div_nonneg (norm_nonneg (f x)) ha.le))
  simpa only [mul_comm] using h

theorem orlicz_truncation_modular_tail {X : Type*} [MeasurableSpace X] {C : ℝ} {μ : Measure X} {f : X → ℂ}
    (hC : 0 ≤ C) (hf : NearOneOrliczMember C μ f) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun m : ℕ => ∫⁻ x, ENNReal.ofReal
      (nearOnePsi C (‖(f-boundedTruncation f m) x‖/t)) ∂μ) atTop (𝓝 0) := by
  obtain ⟨hm, a, ha, hΨ⟩ := hf
  obtain ⟨K, hK, hscale⟩ := nearOnePsi_change_scale hC ha ht
  let bound := fun x => ENNReal.ofReal K*ENNReal.ofReal (nearOnePsi C (‖f x‖/a))
  have hfin : (∫⁻ x, bound x ∂μ) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ne_of_lt ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => nearOnePsi_nonneg C (div_nonneg (norm_nonneg _) ha.le)))).mp hΨ.2)
  have h := tendsto_lintegral_of_dominated_convergence bound
    (fun m => ENNReal.measurable_ofReal.comp ((nearOnePsi_continuous C).measurable.comp
      ((hm.sub (boundedTruncation_measurable hm m)).norm.div_const t)))
    (fun m => Filter.Eventually.of_forall (fun x => by
      dsimp only [bound, Function.comp_apply]
      rw [←ENNReal.ofReal_mul hK.le]
      apply ENNReal.ofReal_le_ofReal
      exact (nearOnePsi_mono C (div_le_div_of_nonneg_right (boundedTruncation_tail_norm_le f m x) ht.le)).trans
        (hscale (‖f x‖) (norm_nonneg _)))) hfin
    (Filter.Eventually.of_forall (fun x => by
      have htail := (boundedTruncation_tail_tendsto f x).norm.div_const t
      have hpsi := (nearOnePsi_continuous C).continuousAt.tendsto.comp htail
      have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpsi
      simpa only [Function.comp_def, norm_zero, zero_div, nearOnePsi_zero, ENNReal.ofReal_zero] using hof))
  simpa only [Function.comp_apply, lintegral_zero] using h

end PrimeSquares
