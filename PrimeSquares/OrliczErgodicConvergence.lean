import PrimeSquares.OrliczMaximalCauchy
import PrimeSquares.ErgodicL1Operators
import PrimeSquares.L1TruncationApproximation
import PrimeSquares.BoundedL1Cauchy
import PrimeSquares.UniformOperatorDensity

set_option autoImplicit false
universe u
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

theorem bounded_truncation_cauchy_from_input (H : RawBoundedSquarePointwiseInput.{u})
    {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (A : PositiveAverageFamily)
    (hA : IsSectionSevenFamily A) {f : X → ℂ} (hf : Measurable f) (m : ℕ) :
    ∀ᵐ x ∂μ, CauchySeq (fun n : ℕ => ergodicPositiveAverage A T n (boundedTruncation f m) x) := by
  have hb := H X μ T hT A hA (boundedTruncation f m) (boundedTruncation_measurable hf m).stronglyMeasurable
    ⟨m, Nat.cast_nonneg m, boundedTruncation_norm_le f m⟩
  filter_upwards [hb] with x hx
  obtain ⟨l, hl⟩ := hx
  exact hl.cauchySeq

theorem orlicz_ergodic_convergence {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (A : PositiveAverageFamily) (hA : IsSectionSevenFamily A)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) {C K : ℝ} (hC : 0 ≤ C)
    (HM : ∀ (g : X → ℂ), Measurable g → ∀ t : ℝ, 0 < t →
      μ {x | ENNReal.ofReal t < ergodicMaximalENorm A T g x} ≤
        ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (nearOnePsi C (‖g x‖/t)) ∂μ))
    {f : X → ℂ} (hf : NearOneOrliczMember C μ f)
    (HB : ∀ m : ℕ, ∀ᵐ x ∂μ,
      CauchySeq (fun n : ℕ => ergodicPositiveAverage A T n (boundedTruncation f m) x)) :
    ∃ g : Lp ℂ 1 μ,
      (∀ n : ℕ, Integrable (ergodicPositiveAverage A T n f) μ) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ergodicPositiveAverage A T n f x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n : ℕ => eLpNorm (ergodicPositiveAverage A T n f-(g : X → ℂ)) 1 μ) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ x, ‖ergodicPositiveAverage A T n f x-g x‖ ∂μ) atTop (𝓝 0) := by
  have hfInt := nearOneOrliczMember_integrable hf hC
  have hfMem : MemLp f 1 μ := memLp_one_iff_integrable.mpr hfInt
  let fL := hfMem.toLp f
  let O := fun n => ergodicSquareL1Operator μ T hT A n
  obtain ⟨v, hv, hvlim⟩ := L1_bounded_truncation_approximation hf.1 hfInt
  have happly (m n : ℕ) : (O n (v m) : X → ℂ) =ᵐ[μ]
      ergodicPositiveAverage A T n (boundedTruncation f m) :=
    (ergodicSquareL1Operator_apply μ T hT A hA n (v m)).trans
      (ergodicPositiveAverage_congr_ae μ T hT A hA n (hv m))
  have hboundedCauchy (m : ℕ) : CauchySeq (fun n : ℕ => O n (v m)) := by
    apply bounded_L1_cauchy_of_ae_cauchy μ
    · intro n
      filter_upwards [happly m n] with x hx
      rw [hx]
      exact ergodicPositiveAverage_norm_bound A T (Nat.cast_nonneg m) (boundedTruncation_norm_le f m) n x
    · filter_upwards [HB m, ae_all_iff.mpr (happly m)] with x hc hx
      have he : (fun n : ℕ => O n (v m) x) =
          (fun n : ℕ => ergodicPositiveAverage A T n (boundedTruncation f m) x) := funext hx
      rwa [he]
  have hCauchy : CauchySeq (fun n : ℕ => O n fL) :=
    uniform_operator_dense_cauchy O (zero_le_one.trans A.mass_one_le)
      (ergodicSquareL1Operator_norm_le μ T hT A) v hvlim hboundedCauchy
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hactual (n : ℕ) : (O n fL : X → ℂ) =ᵐ[μ] ergodicPositiveAverage A T n f :=
    ergodicSquareL1Operator_apply_toLp μ T hT A hA n hfMem
  have hInt (n : ℕ) : Integrable (ergodicPositiveAverage A T n f) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp (O n fL))).congr (hactual n)
  have hIntg : Integrable (g : X → ℂ) μ := memLp_one_iff_integrable.mp (Lp.memLp g)
  have hInMeasure := tendstoInMeasure_of_tendsto_Lp hg
  obtain ⟨ns, hns, hnsAE⟩ := hInMeasure.exists_seq_tendsto_ae
  have hcAE := orlicz_ergodic_ae_cauchy μ A T hC HM hf HB
  have hAE : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ergodicPositiveAverage A T n f x) atTop (𝓝 (g x)) := by
    filter_upwards [hcAE, ae_all_iff.mpr hactual, hnsAE] with x hc hx hsub
    have he : (fun k : ℕ => ergodicPositiveAverage A T (ns k) f x) =
        (fun k : ℕ => O (ns k) fL x) := funext (fun k => (hx (ns k)).symm)
    have hs : Tendsto (fun k : ℕ => ergodicPositiveAverage A T (ns k) f x) atTop (𝓝 (g x)) := by
      rw [he]
      exact hsub
    exact tendsto_nhds_of_cauchySeq_of_subseq hc hns.tendsto_atTop hs
  have hLp : Tendsto (fun n : ℕ => eLpNorm (ergodicPositiveAverage A T n f-(g : X → ℂ)) 1 μ) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hg
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      eLpNorm_congr_ae ((hactual n).sub Filter.EventuallyEq.rfl)))
  have hreal : Tendsto (fun n : ℕ => (eLpNorm (ergodicPositiveAverage A T n f-(g : X → ℂ)) 1 μ).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  refine ⟨g, hInt, hAE, hLp, ?_⟩
  have he (n : ℕ) : (eLpNorm (ergodicPositiveAverage A T n f-(g : X → ℂ)) 1 μ).toReal =
      ∫ x, ‖ergodicPositiveAverage A T n f x-g x‖ ∂μ := by
    have hd := (hInt n).sub hIntg
    rw [eLpNorm_one_eq_lintegral_enorm hd.aestronglyMeasurable]
    simpa only [Pi.sub_apply] using (integral_norm_eq_lintegral_enorm hd.aestronglyMeasurable).symm
  simpa only [he] using hreal

end PrimeSquares
