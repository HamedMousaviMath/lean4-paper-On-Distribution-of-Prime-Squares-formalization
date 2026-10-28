import PrimeSquares.PageDistributionInputs

/-!
# One low/high/error family, fixed before all norm parameters

All three source operators use the same radius and optional Page datum.
The exact identity is proved on every l2 input, and on every l1 input using
the actual l1-to-l-infinity realization of the low operator.
-/

open scoped lp

namespace PrimeSquares

noncomputable def selectedPrimeLowSymbol {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) : C(PrimeCircle, ℂ) :=
  circleLowModel (sourceRationalCenters (sourceMajorArcScale N Q)) N hN
    (optionPageConductor 1 (sourcePageDatum D N Q)) Q
    (conductorMajorant (optionPageConductor 1 (sourcePageDatum D N Q)))
    (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
      (optionPageCharacter 1 (sourcePageDatum D N Q)))
    (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
      (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q))

noncomputable def selectedPrimeLow {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) : ℓ¹(ℤ, ℂ) →L[ℂ] ℓ^⊤(ℤ, ℂ) :=
  fourierL1Operator (selectedPrimeLowSymbol D N hN Q)

noncomputable def selectedPrimeLowL2 {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  integerMultiplier (selectedPrimeLowSymbol D N hN Q)

noncomputable def selectedPrimeHigh {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  pageHighOperator N hN Q (sourceMajorArcScale N Q) (sourcePageDatum D N Q)

noncomputable def selectedPrimeError {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  circleMajorArcErrorOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN
    (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
      (optionPageCharacter 1 (sourcePageDatum D N Q)))
    (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
      (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q))

theorem selectedPrimeLow_agreement {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    selectedPrimeLow D N hN Q f x = selectedPrimeLowL2 D N hN Q
      (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x :=
  fourierL1Operator_all_l2_agreement _ f x

theorem selectedPrime_decomposition_l2 {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt =
      selectedPrimeLowL2 D N hN Q + selectedPrimeHigh D N hN Q + selectedPrimeError D N hN Q := by
  rw [annularWeightedSquareAverage_l2_multiplier]
  rw [annularSymbol_circle_low_high_error _ _ _
    (optionPageConductor 1 (sourcePageDatum D N Q)) Q
    (conductorMajorant (optionPageConductor 1 (sourcePageDatum D N Q)))
    (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
      (optionPageCharacter 1 (sourcePageDatum D N Q)))
    (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
      (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q))]
  rw [integerMultiplier_add, integerMultiplier_add]
  rfl

theorem selectedPrime_decomposition_l1 {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt
      (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x =
      selectedPrimeLow D N hN Q f x +
        selectedPrimeHigh D N hN Q (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x +
        selectedPrimeError D N hN Q (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x := by
  rw [selectedPrime_decomposition_l2, selectedPrimeLow_agreement]
  rfl

noncomputable def selectedPrimeHighTail {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N₀ Q : ℝ) : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  sourcePageDyadicTailOperator N₀ Q (fun j => sourcePageDatum D ((2 : ℕ)^j*2) Q)

theorem selectedPrimeHighTail_of_le {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (N₀ Q : ℝ) (j : ℕ) (hj : N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ)) :
    selectedPrimeHighTail D N₀ Q j = selectedPrimeHigh D ((2 : ℕ)^j*2)
      (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q := by
  simp only [selectedPrimeHighTail, sourcePageDyadicTailOperator, ite_eq_left hj]
  rfl

end PrimeSquares
