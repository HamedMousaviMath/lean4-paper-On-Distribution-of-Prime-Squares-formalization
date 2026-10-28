import PrimeSquares.SelectedPrimeErrorBounds
import PrimeSquares.SelectedPrimeHighBounds

/-!
# Full source Proposition 4.19, as an implication from independent deep inputs

The operators are the fixed selected source operators, not existential maps
chosen separately for each estimate. One positive source coefficient is
chosen before epsilon and every error exponent. The low local clause uses
the literal supremum over all real M>=N, and the high maximum is an actual
real l2 representative of the countable supremum.
-/

open scoped lp

namespace PrimeSquares

/-- All displayed clauses of the source proposition for one common family.
The norm form is the genuine continuous-linear-operator norm, hence implies
the printed function inequalities by `ContinuousLinearMap.le_opNorm`. -/
structure Proposition419Bounds {c : ℝ} (D : PagePrimeSquareDistributionInputs c) (δ : ℝ) : Prop where
  decomposition_l2 : ∀ (N : ℕ) (hN : 1 ≤ N) (Q : ℝ),
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt =
      selectedPrimeLowL2 D N hN Q + selectedPrimeHigh D N hN Q + selectedPrimeError D N hN Q
  low_agreement : ∀ (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ),
    selectedPrimeLow D N hN Q f x = selectedPrimeLowL2 D N hN Q
      (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x
  decomposition_l1 : ∀ (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ),
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt
      (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x =
      selectedPrimeLow D N hN Q f x +
        selectedPrimeHigh D N hN Q (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x +
        selectedPrimeError D N hN Q (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x
  low_norm : ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
    Real.log Q ≤ δ * Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
      ‖selectedPrimeLow D N hN Q‖ ≤
        (2 * lowSpatialConstant) * ((N : ℝ)^2)⁻¹ * Q * Real.log (2*Q)
  low_local : ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
    Real.log Q ≤ δ * Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
    ∀ (f : ℓ¹(ℤ, ℂ)) (x : ℤ), ‖selectedPrimeLow D N hN Q f x‖ ≤
      (8 * lowSpatialConstant * Q * Real.log (2*Q)) * sourceLocalMass N f x
  high : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    (∀ j : ℕ, ∀ Q : ℝ, 2 ≤ Q →
      Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ)) →
      ∀ hN : 1 ≤ (2 : ℕ)^j*2,
        ‖selectedPrimeHigh D ((2 : ℕ)^j*2) hN Q‖ ≤
          K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) ∧
    (∀ Q N₀ : ℝ, 2 ≤ Q → 2 ≤ N₀ → Real.log Q ≤ δ * Real.sqrt (Real.log N₀) →
      ∀ f : ℓ²(ℤ, ℂ), ∃ G : ℓ²(ℤ, ℝ),
        (∀ x, G x = ⨆ j : ℕ, ‖selectedPrimeHighTail D N₀ Q j f x‖) ∧
        (∀ x, 0 ≤ G x) ∧ (∀ j x, ‖selectedPrimeHighTail D N₀ Q j f x‖ ≤ G x) ∧
        ‖G‖ ≤ (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) * ‖f‖ ∧
        (∀ j, ‖selectedPrimeHighTail D N₀ Q j f‖ ≤
          (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) * ‖f‖))
  error : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
      Real.log Q ≤ δ * Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
      ‖selectedPrimeError D N hN Q‖ ≤ K * Q^(-(1/2 : ℝ)) * (1 + Real.log N)^(-A)
  source_high_symbol : ∀ j : ℕ, ∀ Q : ℝ, 2 ≤ Q →
    Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ)) → ∀ ξ : ℝ,
      pageHighSymbol ((2 : ℕ)^j*2)
        (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega)
        Q (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
        (sourcePageDatum D ((2 : ℕ)^j*2) Q) (ξ : PrimeCircle) =
      paperPageHighFrequencyValue ((2 : ℕ)^j*2) Q
        (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
        (sourcePageDatum D ((2 : ℕ)^j*2) Q) ξ

theorem proposition419 (HP : PrimeAsymptoticInputs) {c C : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c) (hC : 0 ≤ C)
    (hBourgain : SmoothCircleBourgainInput C) (hPage : RawPageUniquenessInput c) :
    ∃ δ : ℝ, 0 < δ ∧ Proposition419Bounds D δ := by
  obtain ⟨δL, hδL, hLow⟩ := selectedPrimeLow_source_bounds
  obtain ⟨δH, hδH, hHigh⟩ := selectedPrimeHigh_source_bounds HP D hc hC hBourgain hPage
  obtain ⟨δE, hδE, hError⟩ := selectedPrimeError_all_exponents D
  obtain ⟨δR, hδR, hRaw⟩ := selectedPage_raw_source_range D
  let δ := min δL (min δH (min δE δR))
  have hδ : 0 < δ := lt_min hδL (lt_min hδH (lt_min hδE hδR))
  have hL : δ ≤ δL := min_le_left _ _
  have hH : δ ≤ δH := (min_le_right _ _).trans (min_le_left _ _)
  have hE : δ ≤ δE := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR : δ ≤ δR := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have narrow : ∀ {Q X t : ℝ}, δ ≤ t → Real.log Q ≤ δ * Real.sqrt (Real.log X) →
      Real.log Q ≤ t * Real.sqrt (Real.log X) := by
    intro Q X t ht hcut
    exact hcut.trans (mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg _))
  refine ⟨δ, hδ, {
    decomposition_l2 := selectedPrime_decomposition_l2 D
    low_agreement := selectedPrimeLow_agreement D
    decomposition_l1 := selectedPrime_decomposition_l1 D
    low_norm := ?_
    low_local := ?_
    high := ?_
    error := ?_
    source_high_symbol := ?_ }⟩
  · intro N hn Q hQ hcut hN
    exact (hLow D N hn Q hQ (narrow hL hcut) hN).1
  · intro N hn Q hQ hcut hN f x
    exact (hLow D N hn Q hQ (narrow hL hcut) hN).2 f x
  · intro ε hε
    obtain ⟨K, hK, hfixed, hmax⟩ := hHigh ε hε
    refine ⟨K, hK, ?_, ?_⟩
    · intro j Q hQ hcut hN
      exact hfixed j Q hQ (narrow hH hcut) hN
    · intro Q N₀ hQ hN₀ hcut f
      obtain ⟨G, heq, h0, ht, hn, hf, _⟩ := hmax Q N₀ hQ hN₀ (narrow hH hcut) f
      exact ⟨G, heq, h0, ht, hn, hf⟩
  · intro A hA
    obtain ⟨K, hK, herr⟩ := hError A hA.le
    refine ⟨K, hK, ?_⟩
    intro N hn Q hQ hcut hN
    have hAd : SourcePageRawAdmissible D N Q :=
      hRaw Q N hQ (by exact_mod_cast hn) (narrow hR hcut) N le_rfl
    exact herr N hn Q hQ (narrow hE hcut) hAd hN
  · intro j Q hQ hcut ξ
    obtain ⟨K, _, _, hmax⟩ := hHigh 1 (by norm_num)
    have hN : (2 : ℕ) ≤ 2^j*2 := dyadic_annular_scale_lower (M := 2) (by norm_num) j
    obtain ⟨G, _, _, _, _, _, hsource⟩ := hmax Q (((2 : ℕ)^j*2 : ℕ) : ℝ) hQ
      (by exact_mod_cast hN) (narrow hH hcut) (0 : ℓ²(ℤ, ℂ))
    exact hsource j le_rfl ξ

/-- The N=1 dyadic scale cannot satisfy the source range with Q>=2.
Consequently the j+1 indexing in the high clause covers every admissible
dyadic scale in the original source statement. -/
theorem proposition419_dyadic_coverage {k : ℕ} {Q δ : ℝ} (hQ : 2 ≤ Q)
    (hcut : Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^k : ℕ) : ℝ))) :
    ∃ j : ℕ, (2 : ℕ)^j*2 = (2 : ℕ)^k := by
  have hk : 1 ≤ k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz, pow_zero, Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero] at hcut
    have hp : 0 < Real.log Q := Real.log_pos (by linarith)
    linarith
  refine ⟨k-1, ?_⟩
  rw [← pow_succ, Nat.sub_add_cancel hk]

end PrimeSquares
