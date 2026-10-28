import PrimeSquares.OrliczTruncation
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace PrimeSquares

def tailOscillationSet {X : Type*} (v : ℕ → X → ℂ) (e : ℝ) : Set X :=
  {x | ∀ J : ℕ, ∃ n : ℕ, J ≤ n ∧ ∃ m : ℕ, J ≤ m ∧ e ≤ ‖v n x-v m x‖}

theorem tailOscillation_not_mem {X : Type*} [MeasurableSpace X]
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) (f g : X → ℂ) (x : X)
    {e : ℝ} (he : 0 < e)
    (hg : CauchySeq (fun n : ℕ => ergodicPositiveAverage A T n g x))
    (herr : ergodicMaximalENorm A T (f-g) x ≤ ENNReal.ofReal (e/4)) :
    x ∉ tailOscillationSet (fun n => ergodicPositiveAverage A T n f) e := by
  intro hbad
  obtain ⟨J, hJ⟩ := Metric.cauchySeq_iff.mp hg (e/4) (by positivity)
  obtain ⟨n, hn, m, hm, hval⟩ := hbad J
  have hN := (ergodicMaximalENorm_dominates A T (f-g) n x).trans herr
  have hM := (ergodicMaximalENorm_dominates A T (f-g) m x).trans herr
  rw [←ofReal_norm] at hN hM
  have hN' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ e/4)).mp hN
  have hM' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ e/4)).mp hM
  have hG : ‖ergodicPositiveAverage A T n g x-ergodicPositiveAverage A T m g x‖ < e/4 := by
    simpa only [dist_eq_norm] using hJ n hn m hm
  have heq : ergodicPositiveAverage A T n f x-ergodicPositiveAverage A T m f x =
      (ergodicPositiveAverage A T n (f-g) x+
        (ergodicPositiveAverage A T n g x-ergodicPositiveAverage A T m g x))-
        ergodicPositiveAverage A T m (f-g) x := by
    rw [ergodicPositiveAverage_sub, ergodicPositiveAverage_sub]
    abel
  have htriangle := (norm_sub_le
    (ergodicPositiveAverage A T n (f-g) x+
      (ergodicPositiveAverage A T n g x-ergodicPositiveAverage A T m g x))
    (ergodicPositiveAverage A T m (f-g) x)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [←heq] at htriangle
  nlinarith

theorem ae_cauchySeq_of_tailOscillation_null {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : ℕ → X → ℂ) (H : ∀ e : ℝ, 0 < e → μ (tailOscillationSet v e) = 0) :
    ∀ᵐ x ∂μ, CauchySeq (fun n : ℕ => v n x) := by
  have hgood (j : ℕ) : ∀ᵐ x ∂μ, x ∉ tailOscillationSet v (1/((j : ℝ)+1)) := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using H (1/((j : ℝ)+1)) (by positivity)
  filter_upwards [ae_all_iff.mpr hgood] with x hx
  apply Metric.cauchySeq_iff.mpr
  intro e he
  obtain ⟨j, hj⟩ := exists_nat_gt (1/e)
  have hsmall : 1/((j : ℝ)+1) < e := by
    apply (div_lt_iff₀ (by positivity : 0 < (j : ℝ)+1)).mpr
    have h := (div_lt_iff₀ he).mp hj
    nlinarith
  have hnot := hx j
  change ¬(∀ J : ℕ, ∃ n : ℕ, J ≤ n ∧ ∃ m : ℕ, J ≤ m ∧
    1/((j : ℝ)+1) ≤ ‖v n x-v m x‖) at hnot
  push Not at hnot
  obtain ⟨J, hJ⟩ := hnot
  refine ⟨J, ?_⟩
  intro n hn m hm
  rw [dist_eq_norm]
  exact (hJ n hn m hm).trans hsmall

theorem orlicz_ergodic_ae_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : PositiveAverageFamily) (T : X ≃ᵐ X) {C K : ℝ} (hC : 0 ≤ C)
    (HM : ∀ (g : X → ℂ), Measurable g → ∀ t : ℝ, 0 < t →
      μ {x | ENNReal.ofReal t < ergodicMaximalENorm A T g x} ≤
        ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (nearOnePsi C (‖g x‖/t)) ∂μ))
    {f : X → ℂ} (hf : NearOneOrliczMember C μ f)
    (HB : ∀ m : ℕ, ∀ᵐ x ∂μ,
      CauchySeq (fun n : ℕ => ergodicPositiveAverage A T n (boundedTruncation f m) x)) :
    ∀ᵐ x ∂μ, CauchySeq (fun n : ℕ => ergodicPositiveAverage A T n f x) := by
  apply ae_cauchySeq_of_tailOscillation_null μ
  intro e he
  have hbound (m : ℕ) : μ (tailOscillationSet (fun n => ergodicPositiveAverage A T n f) e) ≤
      ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal
        (nearOnePsi C (‖(f-boundedTruncation f m) x‖/(e/4))) ∂μ) := by
    have hsub : ∀ᵐ x ∂μ, x ∈ tailOscillationSet (fun n => ergodicPositiveAverage A T n f) e →
        x ∈ {x | ENNReal.ofReal (e/4) < ergodicMaximalENorm A T (f-boundedTruncation f m) x} := by
      filter_upwards [HB m] with x hx hbad
      by_contra herr
      exact (tailOscillation_not_mem A T f (boundedTruncation f m) x he hx (le_of_not_gt herr)) hbad
    exact (measure_mono_ae hsub).trans (HM (f-boundedTruncation f m)
      (hf.1.sub (boundedTruncation_measurable hf.1 m)) (e/4) (by positivity))
  have ht := orlicz_truncation_modular_tail hC hf (by positivity : 0 < e/4)
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) ht (Or.inr ENNReal.ofReal_ne_top)
  have hz := ge_of_tendsto' hlim hbound
  simpa only [mul_zero, nonpos_iff_eq_zero] using hz

end PrimeSquares
