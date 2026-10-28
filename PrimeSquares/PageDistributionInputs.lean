import PrimeSquares.PrimeSquareDistributionInputs
import PrimeSquares.Proposition621Source

/-!
# Compatible raw distribution data for the maximal assembly

This refines the existing independent distribution hypothesis to return an
actual optional primitive real character with a genuine zero in the Page
region. It assumes only the raw progression and exponential-sum inputs;
no approximation, decomposition or maximal conclusion is a field.
The selection depends on N and Q, never on an error exponent or epsilon.
-/

namespace PrimeSquares

theorem optionPageConductor_pos (E : Option PageZeroDatum) :
    0 < optionPageConductor 1 E := by
  cases E with
  | none => norm_num [optionPageConductor]
  | some F => exact lt_of_lt_of_le (by norm_num) F.conductor_two

theorem optionPageCharacter_quadratic (E : Option PageZeroDatum) :
    (optionPageCharacter 1 E).IsQuadratic := by
  cases E with
  | none => exact MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp [optionPageCharacter])
  | some F => exact F.quadratic

structure PagePrimeSquareDistributionInputs (pageConstant : ℝ) where
  progressionConstant : ℝ
  renConstant : ℝ
  ghoshConstant : ℝ
  renPower : ℝ
  decayConstant : ℝ
  progression_nonneg : 0 ≤ progressionConstant
  ren_nonneg : 0 ≤ renConstant
  ghosh_nonneg : 0 ≤ ghoshConstant
  renPower_nonneg : 0 ≤ renPower
  decay_pos : 0 < decayConstant
  startingScale : ℕ
  raw_data : ∀ N : ℕ, startingScale ≤ N → ∀ Q : ℝ, 2 ≤ Q →
    Real.log Q ≤ (min (decayConstant/7) 1/8)*Real.sqrt (Real.log N) →
    ∃ E : Option PageZeroDatum,
      (∀ F, E = some F → (F.conductor : ℝ) ≤ sourceMajorArcScale N Q ∧
        1-(pageConstant/2)/Real.log (sourceMajorArcScale N Q) < F.beta) ∧
      CircleAnalyticInputs N Q
        (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
        (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)
        progressionConstant renConstant ghoshConstant renPower decayConstant

noncomputable def PagePrimeSquareDistributionInputs.toFixedScale {c : ℝ}
    (D : PagePrimeSquareDistributionInputs c) : PrimeSquareDistributionInputs where
  progressionConstant := D.progressionConstant
  renConstant := D.renConstant
  ghoshConstant := D.ghoshConstant
  renPower := D.renPower
  decayConstant := D.decayConstant
  progression_nonneg := D.progression_nonneg
  ren_nonneg := D.ren_nonneg
  ghosh_nonneg := D.ghosh_nonneg
  renPower_nonneg := D.renPower_nonneg
  decay_pos := D.decay_pos
  startingScale := D.startingScale
  raw_data := by
    intro N hN Q hQ hcut
    obtain ⟨E, _, hraw⟩ := D.raw_data N hN Q hQ hcut
    exact ⟨optionPageConductor 1 E, optionPageConductor_pos E,
      optionPageCharacter 1 E, optionPageCharacter_quadratic E, E.isSome, optionPageBeta E, hraw⟩

def SourcePageRawAdmissible {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (Q : ℝ) : Prop :=
  D.startingScale ≤ N ∧ 2 ≤ Q ∧
    Real.log Q ≤ (min (D.decayConstant/7) 1/8)*Real.sqrt (Real.log N)

noncomputable def sourcePageDatum {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (Q : ℝ) : Option PageZeroDatum := by
  classical
  exact if h : SourcePageRawAdmissible D N Q then
    Classical.choose (D.raw_data N h.1 Q h.2.1 h.2.2) else none

theorem sourcePageDatum_spec {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (Q : ℝ) (h : SourcePageRawAdmissible D N Q) :
    (∀ F, sourcePageDatum D N Q = some F →
      (F.conductor : ℝ) ≤ sourceMajorArcScale N Q ∧
      1-(c/2)/Real.log (sourceMajorArcScale N Q) < F.beta) ∧
    CircleAnalyticInputs N Q
      (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
        (optionPageCharacter 1 (sourcePageDatum D N Q)))
      (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
        (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q))
      D.progressionConstant D.renConstant D.ghoshConstant D.renPower D.decayConstant := by
  classical
  unfold sourcePageDatum
  rw [dite_eq_left h]
  exact Classical.choose_spec (D.raw_data N h.1 Q h.2.1 h.2.2)

theorem pageDistribution_cutoff_pos {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    0 < (min (D.decayConstant/7) 1)/8 :=
  distribution_cutoff_constant_pos D.toFixedScale

end PrimeSquares
