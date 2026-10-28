import PrimeSquares.TheoremOneFive
import PrimeSquares.GranvilleKurlbergInterface
import PrimeSquares.OddSquarefreeUnitSquareFormulas

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped Topology
namespace PrimeSquares

theorem source_lavictoire_persistent_criterion
    (HL : RawOriginalLaVictoireInput.{u}) (HS : RawSawyerMaximalInput.{u})
    (HC : RawConzeMaximalInput.{u}) (n : ℕ → ℕ)
    (HA : Nonempty (LaVictoireArithmetic n)) : PersistentUniversalL1Bad.{u} n :=
  persistent_l1_badness_from_arithmetic HL HS HC n HA

theorem theorem_1_5_i_literal
    (HW : RawSplitQuadraticWeilInput) (HPNT : RawFixedPrimeProgressionFrequencyInput)
    (HL : RawOriginalLaVictoireInput.{u}) (HS : RawSawyerMaximalInput.{u})
    (HC : RawConzeMaximalInput.{u})
    (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hμ : NonatomicMeasure μ) (hT : Ergodic T μ)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ f : X → ℂ, Measurable f ∧ Integrable f μ ∧
      ∃ E : Set X, MeasurableSet E ∧ 0 < μ E ∧ ∀ x ∈ E,
        ¬ ∃ L : ℂ, Tendsto
          (fun j => (Nat.nth (fun N => N ∈ S) j:ℂ)⁻¹*
            ∑ k ∈ Finset.range (Nat.nth (fun N => N ∈ S) j),
              f ((T^[(Nat.nth Nat.Prime k)^2]) x)) atTop (𝓝 L) :=
  theorem_1_5_i HW HPNT HL HS HC X μ T hμ hT S hS

theorem section_eight_complete
    (HW : RawSplitQuadraticWeilInput) (HPNT : RawFixedPrimeProgressionFrequencyInput)
    (HL : RawOriginalLaVictoireInput.{u}) (HS : RawSawyerMaximalInput.{u})
    (HC : RawConzeMaximalInput.{u}) (HG : RawGranvilleKurlbergInput) :
    Nonempty (LaVictoireArithmetic primeSquareSequence) ∧
      PersistentUniversalL1Bad.{u} primeSquareSequence ∧
      CyclicPoissonSpacings unitSquareFamily badnessQPos :=
  ⟨primeSquare_lavictoire_arithmetic HW HPNT,
    theorem_1_5_i HW HPNT HL HS HC,unitSquareBlock_poisson HW HG⟩

end PrimeSquares
