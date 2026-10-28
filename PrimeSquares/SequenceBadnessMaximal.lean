import PrimeSquares.LaVictoireArithmetic
import PrimeSquares.ErgodicStrongMaximal
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
universe u
open Finset Filter MeasureTheory
open scoped Topology ENNReal
namespace PrimeSquares

def NonatomicMeasure {X : Type u} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ A : Set X, MeasurableSet A → 0 < μ A →
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < μ B ∧ μ B < μ A

noncomputable def sequenceErgodicAverage {X : Type u} (n : ℕ → ℕ) (T : X → X)
    (N : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  (N:ℂ)⁻¹*∑ k ∈ Finset.range N, f ((T^[n k]) x)

noncomputable def restrictedSequenceMax {X : Type u} (n : ℕ → ℕ) (S : Set ℕ)
    (T : X → X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ N : S, ‖sequenceErgodicAverage n T N.val f x‖ₑ

noncomputable def sequenceAveragesOn {X : Type u} (n : ℕ → ℕ) (S : Set ℕ)
    (T : X → X) (f : X → ℂ) (x : X) (j : ℕ) : ℂ :=
  sequenceErgodicAverage n T (Nat.nth (fun N => N ∈ S) j) f x

theorem sequenceErgodicAverage_measurable {X : Type u} [MeasurableSpace X]
    (n : ℕ → ℕ) (T : X → X) (hT : Measurable T) (N : ℕ) (f : X → ℂ)
    (hf : Measurable f) : Measurable (sequenceErgodicAverage n T N f) := by
  unfold sequenceErgodicAverage
  fun_prop

theorem restrictedSequenceMax_measurable {X : Type u} [MeasurableSpace X]
    (n : ℕ → ℕ) (S : Set ℕ) (T : X → X) (hT : Measurable T) (f : X → ℂ)
    (hf : Measurable f) : Measurable (restrictedSequenceMax n S T f) := by
  apply Measurable.iSup
  intro N
  exact (sequenceErgodicAverage_measurable n T hT N.val f hf).enorm

theorem restrictedSequenceMax_enumeration {X : Type u} (n : ℕ → ℕ) (S : Set ℕ)
    (hS : S.Infinite) (T : X → X) (f : X → ℂ) (x : X) :
    restrictedSequenceMax n S T f x=⨆ j : ℕ, ‖sequenceAveragesOn n S T f x j‖ₑ := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro N
    have heq : Nat.nth (fun N => N ∈ S) (Nat.count (fun N => N ∈ S) N.val)=N.val :=
      Nat.nth_count N.property
    simpa only [sequenceAveragesOn, heq] using
      (le_iSup (fun j => ‖sequenceAveragesOn n S T f x j‖ₑ)
        (Nat.count (fun N => N ∈ S) N.val))
  · apply iSup_le
    intro j
    exact le_iSup (fun N : S => ‖sequenceErgodicAverage n T N.val f x‖ₑ)
      ⟨Nat.nth (fun N => N ∈ S) j,Nat.nth_mem_of_infinite hS j⟩

theorem convergent_sequence_enorm_sup_finite (v : ℕ → ℂ) (L : ℂ)
    (hv : Tendsto v atTop (𝓝 L)) : (⨆ j, ‖v j‖ₑ)<∞ := by
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
  have hbound : (⨆ j, ‖v j‖ₑ) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro j
    rw [←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨j,rfl⟩)
  exact hbound.trans_lt ENNReal.ofReal_lt_top

theorem maximal_infinite_implies_divergence {X : Type u} (n : ℕ → ℕ) (S : Set ℕ)
    (hS : S.Infinite) (T : X → X) (f : X → ℂ) (x : X)
    (hx : restrictedSequenceMax n S T f x=∞) :
    ¬ ∃ L : ℂ, Tendsto (sequenceAveragesOn n S T f x) atTop (𝓝 L) := by
  rintro ⟨L,hL⟩
  have hfinite := convergent_sequence_enorm_sup_finite _ L hL
  rw [←restrictedSequenceMax_enumeration n S hS T f x,hx] at hfinite
  exact (lt_irrefl _ hfinite)

end PrimeSquares
