import PrimeSquares.SequenceBadnessMaximal

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped Topology ENNReal
namespace PrimeSquares

def SystemSequenceWeakBound {X : Type u} [MeasurableSpace X] (n : ℕ → ℕ)
    (S : Set ℕ) (C : ℝ) (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, Measurable f → Integrable f μ → ∀ t : ℝ, 0 < t →
    μ {x | ENNReal.ofReal t < restrictedSequenceMax n S T f x} ≤
      ENNReal.ofReal (C/t*(∫ x, ‖f x‖ ∂μ))

def UniversalSequenceWeakBound (n : ℕ → ℕ) (S : Set ℕ) (C : ℝ) : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X), MeasurePreserving T μ μ → SystemSequenceWeakBound n S C μ T

def RawOriginalLaVictoireInput : Prop :=
  ∀ n : ℕ → ℕ, Nonempty (LaVictoireArithmetic n) → ∀ S : Set ℕ, S.Infinite →
    ∀ C : ℝ, 0 < C → ¬ UniversalSequenceWeakBound.{u} n S C

def RawSawyerMaximalInput : Prop :=
  ∀ (n : ℕ → ℕ) (S : Set ℕ), S.Infinite →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X → X), NonatomicMeasure μ → Ergodic T μ →
      (∀ f : X → ℂ, Measurable f → Integrable f μ →
        ∀ᵐ x ∂μ, restrictedSequenceMax n S T f x < ∞) →
      ∃ C : ℝ, 0 < C ∧ SystemSequenceWeakBound n S C μ T

def RawConzeMaximalInput : Prop :=
  ∀ (n : ℕ → ℕ) (S : Set ℕ), S.Infinite → ∀ C : ℝ, 0 < C →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X → X), NonatomicMeasure μ → Ergodic T μ →
      SystemSequenceWeakBound n S C μ T → UniversalSequenceWeakBound.{u} n S C

def PersistentUniversalL1Bad (n : ℕ → ℕ) : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X), NonatomicMeasure μ → Ergodic T μ →
    ∀ S : Set ℕ, S.Infinite → ∃ f : X → ℂ, Measurable f ∧ Integrable f μ ∧
      ∃ E : Set X, MeasurableSet E ∧ 0 < μ E ∧
        ∀ x ∈ E, ¬ ∃ L : ℂ, Tendsto (sequenceAveragesOn n S T f x) atTop (𝓝 L)

theorem weak_failure_produces_infinite_maximal
    (HL : RawOriginalLaVictoireInput.{u}) (HS : RawSawyerMaximalInput.{u})
    (HC : RawConzeMaximalInput.{u}) (n : ℕ → ℕ)
    (HA : Nonempty (LaVictoireArithmetic n)) (S : Set ℕ) (hS : S.Infinite)
    (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hμ : NonatomicMeasure μ) (hT : Ergodic T μ) :
    ∃ f : X → ℂ, Measurable f ∧ Integrable f μ ∧
      ∃ E : Set X, MeasurableSet E ∧ 0 < μ E ∧
        ∀ x ∈ E, restrictedSequenceMax n S T f x=∞ := by
  classical
  have hnot : ¬ ∀ f : X → ℂ, Measurable f → Integrable f μ →
      ∀ᵐ x ∂μ, restrictedSequenceMax n S T f x<∞ := by
    intro hfinite
    obtain ⟨C,hC,hweak⟩ := HS n S hS X μ T hμ hT hfinite
    exact HL n HA S hS C hC (HC n S hS C hC X μ T hμ hT hweak)
  push Not at hnot
  obtain ⟨f,hf,hfi,hnot⟩ := hnot
  have hne : μ {x | restrictedSequenceMax n S T f x=∞}≠0 := by
    intro hz
    apply hnot
    rw [ae_iff]
    simpa only [not_lt, top_le_iff, not_not] using hz
  refine ⟨f,hf,hfi,{x | restrictedSequenceMax n S T f x=∞},?_,pos_iff_ne_zero.mpr hne,?_⟩
  · exact measurableSet_eq_fun (restrictedSequenceMax_measurable n S T hT.measurable f hf)
      measurable_const
  · intro x hx
    exact hx

theorem persistent_l1_badness_from_arithmetic
    (HL : RawOriginalLaVictoireInput.{u}) (HS : RawSawyerMaximalInput.{u})
    (HC : RawConzeMaximalInput.{u}) (n : ℕ → ℕ)
    (HA : Nonempty (LaVictoireArithmetic n)) : PersistentUniversalL1Bad.{u} n := by
  intro X _ μ _ T hμ hT S hS
  obtain ⟨f,hf,hfi,E,hE,hEpos,hInf⟩ :=
    weak_failure_produces_infinite_maximal HL HS HC n HA S hS X μ T hμ hT
  exact ⟨f,hf,hfi,E,hE,hEpos,fun x hx =>
    maximal_infinite_implies_divergence n S hS T f x (hInf x hx)⟩

end PrimeSquares
