import PrimeSquares.ErgodicSquareAverages
import PrimeSquares.CorollarySevenSix

set_option autoImplicit false
universe u
open MeasureTheory Set
open scoped ENNReal Topology lp
namespace PrimeSquares

def PositiveModularBound (A : PositiveAverageFamily) (Φ : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
    ∀ t : ℝ, 0 < t → Measure.count {x | t < positiveMaximal A f x} ≤
      ENNReal.ofReal K*∑ x ∈ F, ENNReal.ofReal (Φ (‖f x‖/t))

/-- Independent general strong Calderon transference; its existence and
published-theorem bridge are not proved by this interface. -/
def RawCalderonStrongInput : Prop :=
  ∀ (A : PositiveAverageFamily) (p B : ℝ), 1 < p → 0 ≤ B → PositiveStrongMaximalBound A p B →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X), MeasurePreserving T μ μ →
      ∀ f : X → ℂ, MemLp f (ENNReal.ofReal p) μ →
        (∀ᵐ x ∂μ, ergodicMaximalENorm A T f x < ∞) ∧
        MemLp (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ∧
        eLpNorm (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal B*eLpNorm f (ENNReal.ofReal p) μ

/-- Independent general modular Calderon transference, for arbitrary continuous
nonnegative gauges vanishing at zero, with no arithmetic endpoint conclusion. -/
def RawCalderonModularInput : Prop :=
  ∀ (A : PositiveAverageFamily) (Φ : ℝ → ℝ) (K : ℝ), 0 ≤ K → Continuous Φ →
    Φ 0 = 0 → (∀ t : ℝ, 0 ≤ t → 0 ≤ Φ t) → PositiveModularBound A Φ K →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X), MeasurePreserving T μ μ →
      ∀ f : X → ℂ, AEStronglyMeasurable f μ → ∀ t : ℝ, 0 < t →
        μ {x | ENNReal.ofReal t < ergodicMaximalENorm A T f x} ≤
          ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (Φ (‖f x‖/t)) ∂μ)

/-- Independent bounded-class polynomial convergence, including the still
unformalized one-dimensional and normalization bridge from the published
standard theorem. It asserts no unbounded Orlicz convergence. -/
def RawBoundedSquarePointwiseInput : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X ≃ᵐ X), MeasurePreserving T μ μ →
    ∀ A : PositiveAverageFamily, IsSectionSevenFamily A →
      ∀ g : X → ℂ, StronglyMeasurable g →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖g x‖ ≤ B) →
        ∀ᵐ x ∂μ, ∃ l : ℂ, Filter.Tendsto (fun n : ℕ => ergodicPositiveAverage A T n g x)
          Filter.atTop (𝓝 l)

theorem calderon_strong_apply (H : RawCalderonStrongInput.{u})
    (A : PositiveAverageFamily) {p B : ℝ} (hp : 1 < p) (hB : 0 ≤ B)
    (HD : PositiveStrongMaximalBound A p B)
    {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) {f : X → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∀ᵐ x ∂μ, ergodicMaximalENorm A T f x < ∞) ∧
      MemLp (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ∧
      eLpNorm (ergodicMaximalValue A T f) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal B*eLpNorm f (ENNReal.ofReal p) μ :=
  H A p B hp hB HD X μ T hT f hf

end PrimeSquares
