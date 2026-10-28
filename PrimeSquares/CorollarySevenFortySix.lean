import PrimeSquares.OrliczErgodicConvergence
import PrimeSquares.CorollarySevenSix
import PrimeSquares.ErgodicModularMaximal

set_option autoImplicit false
universe u
open MeasureTheory Filter
open scoped ENNReal Topology
namespace PrimeSquares

def ErgodicOrliczConclusion (C K : ℝ) : Prop :=
  ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X), MeasurePreserving T μ μ →
      (∀ p : ℝ, 1 < p → p ≤ 2 → ∀ f : X → ℂ, MemLp f (ENNReal.ofReal p) μ →
        (∀ᵐ x ∂μ, ergodicMaximalENorm A T f x < ∞) ∧
        MemLp (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ∧
        eLpNorm (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Real.exp (C/(p-1)*Real.log (Real.exp 1/(p-1))))*eLpNorm f (ENNReal.ofReal p) μ ∧
        (eLpNorm (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ).toReal ≤
          Real.exp (C/(p-1)*Real.log (Real.exp 1/(p-1)))*(eLpNorm f (ENNReal.ofReal p) μ).toReal) ∧
      (∀ f : X → ℂ, AEStronglyMeasurable f μ → ∀ t : ℝ, 0 < t →
        μ {x | ENNReal.ofReal t < ergodicMaximalENorm A T f x} ≤
          ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (nearOnePsi C (‖f x‖/t)) ∂μ)) ∧
      (∀ f : X → ℂ, NearOneOrliczMember C μ f → ∃ g : Lp ℂ 1 μ,
        (∀ n : ℕ, Integrable (ergodicPositiveAverage A T n f) μ) ∧
        (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ergodicPositiveAverage A T n f x) atTop (𝓝 (g x))) ∧
        Tendsto (fun n : ℕ => eLpNorm (ergodicPositiveAverage A T n f-(g : X → ℂ)) 1 μ) atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫ x, ‖ergodicPositiveAverage A T n f x-g x‖ ∂μ) atTop (𝓝 0))

theorem section7_ergodic_assembly (HStrong : RawCalderonStrongInput.{u})
    (HModular : RawCalderonModularInput.{u}) (HBounded : RawBoundedSquarePointwiseInput.{u})
    {C C₀ K : ℝ} (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (hK : 1 ≤ K)
    (H : SectionSevenOrliczConclusion C C₀ K) :
    ∃ Cfinal Kfinal : ℝ, 1 ≤ Cfinal ∧ 1 ≤ Kfinal ∧ ErgodicOrliczConclusion.{u} Cfinal Kfinal := by
  obtain ⟨D, hD, hDiscrete⟩ := section7_strong_assembly hC hC₀ hK H
  let Cfinal := max C D+1
  have hCC : C ≤ Cfinal := by dsimp [Cfinal]; linarith [le_max_left C D]
  have hDC : D ≤ Cfinal := by dsimp [Cfinal]; linarith [le_max_right C D]
  have hCfinal : 1 ≤ Cfinal := hC.trans hCC
  have hK0 : 0 ≤ K := by linarith
  refine ⟨Cfinal, K, hCfinal, hK, ?_⟩
  intro A hA X _ μ _ T hT
  have hmod (f : X → ℂ) (hf : AEStronglyMeasurable f μ) (t : ℝ) (ht : 0 < t) :=
    section7_ergodic_modular_apply HModular hCC hK0 H A hA μ T hT hf ht
  refine ⟨?_, hmod, ?_⟩
  · intro p hp hp2 f hf
    obtain ⟨hfinite, hmem, hnorm⟩ := calderon_strong_apply HStrong A hp (Real.exp_pos _).le
      (hDiscrete A hA p hp hp2) μ T hT hf
    have hrate : Real.exp (D/(p-1)*Real.log (Real.exp 1/(p-1))) ≤
        Real.exp (Cfinal/(p-1)*Real.log (Real.exp 1/(p-1))) := by
      apply Real.exp_le_exp.mpr
      have hL := (nearOne_log_reciprocal_bounds (by linarith : 0 < p-1) (by linarith : p-1 ≤ 1)).1
      have h := mul_le_mul_of_nonneg_right hDC (show 0 ≤ (1/(p-1))*Real.log (Real.exp 1/(p-1)) by linarith)
      convert h using 1 <;> ring
    have hn := hnorm.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hrate) _)
    refine ⟨hfinite, hmem, hn, ?_⟩
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) hn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr
  · intro f hf
    exact orlicz_ergodic_convergence μ A hA T hT (by linarith : 0 ≤ Cfinal)
      (fun g hg t ht => hmod g hg.aestronglyMeasurable t ht) hf
      (bounded_truncation_cauchy_from_input HBounded μ T hT A hA hf.1)

theorem corollary_7_46 {c C Cb E Z R H S : ℝ}
    (D : PagePrimeSquareDistributionInputs c)
    (hC : 2 ≤ C) (hCe : Real.exp 1 ≤ C) (hCb : 0 ≤ Cb)
    (HB : SmoothCircleBourgainInput Cb) (hE : 0 ≤ E) (HE : RawQuadraticWeylApproximationInput E) (hc : 0 < c) (HP : RawPageUniquenessInput c)
    (HT : RawTaoArcConstructionInput C)
    (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (HIW : RawIWMultiplierInput C) (HCZ : RawScalarHormanderInput Z) (HY : RawYoungMultiplierInput)
    (HRM : RawFiniteSignedMaximalInput R) (Hmajor : RawMajorArcSamplingInput C)
    (HShannon : RawNarrowShannonInput S) (HHL : RawOneSidedHLInput H) (HRT : RawRieszThorinMultiplierInput)
    (HStrong : RawCalderonStrongInput.{u}) (HModular : RawCalderonModularInput.{u})
    (HBounded : RawBoundedSquarePointwiseInput.{u}) :
    ∃ Cfinal Kfinal : ℝ, 1 ≤ Cfinal ∧ 1 ≤ Kfinal ∧ ErgodicOrliczConclusion.{u} Cfinal Kfinal := by
  obtain ⟨Cg, C₀, K, hCg, hC₀, hK, hT⟩ := theorem_7_2 D hC hCe hCb HB hE HE hc HP HT
    hZ hR hH hS HIW HCZ HY HRM Hmajor HShannon HHL HRT
  exact section7_ergodic_assembly HStrong HModular HBounded hCg hC₀ hK hT

end PrimeSquares
