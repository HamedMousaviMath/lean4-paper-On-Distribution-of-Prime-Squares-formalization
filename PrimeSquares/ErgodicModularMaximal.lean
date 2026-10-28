import PrimeSquares.ErgodicIndependentInputs

set_option autoImplicit false
universe u
open MeasureTheory Set Finset
open scoped ENNReal
namespace PrimeSquares

theorem section7_positive_modular_bound {C C₀ K D : ℝ}
    (hCD : C ≤ D) (hK : 0 ≤ K) (H : SectionSevenOrliczConclusion C C₀ K)
    (A : PositiveAverageFamily) (hA : IsSectionSevenFamily A) :
    PositiveModularBound A (nearOnePsi D) K := by
  intro F f hf t ht
  obtain ⟨hfinite, hcard⟩ := (H A hA).2.1 F f hf t ht
  have hcount : Measure.count {x | t < positiveMaximal A f x} =
      ENNReal.ofReal ({x | t < positiveMaximal A f x}.ncard : ℝ) := by
    rw [Measure.count_apply_finite _ hfinite, Set.ncard_eq_toFinset_card _ hfinite]
    simp only [ENNReal.ofReal_natCast]
  calc
    _ = _ := hcount
    _ ≤ ENNReal.ofReal (K*∑ x ∈ F, nearOnePsi C (‖f x‖/t)) := ENNReal.ofReal_le_ofReal hcard
    _ ≤ ENNReal.ofReal (K*∑ x ∈ F, nearOnePsi D (‖f x‖/t)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun x _ =>
        nearOnePsi_mono_coefficient hCD (div_nonneg (norm_nonneg _) ht.le))) hK
    _ = _ := by
      rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg
        (fun x _ => nearOnePsi_nonneg _ (div_nonneg (norm_nonneg _) ht.le))]

theorem section7_ergodic_modular_apply (HC : RawCalderonModularInput.{u}) {C C₀ K D : ℝ}
    (hCD : C ≤ D) (hK : 0 ≤ K) (H : SectionSevenOrliczConclusion C C₀ K)
    (A : PositiveAverageFamily) (hA : IsSectionSevenFamily A)
    {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) {t : ℝ} (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < ergodicMaximalENorm A T f x} ≤
      ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (nearOnePsi D (‖f x‖/t)) ∂μ) :=
  HC A (nearOnePsi D) K hK (nearOnePsi_continuous D) (nearOnePsi_zero D)
    (fun _ ht => nearOnePsi_nonneg D ht) (section7_positive_modular_bound hCD hK H A hA)
    X μ T hT f hf t ht

end PrimeSquares
