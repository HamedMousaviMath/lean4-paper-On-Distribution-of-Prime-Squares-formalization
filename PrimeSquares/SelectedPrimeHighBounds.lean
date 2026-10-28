import PrimeSquares.SelectedPrimeLowBounds

/-!
# The selected family satisfies both sharp source high estimates

One cutoff coefficient is chosen before epsilon. The same K controls every
fixed dyadic scale and the actual countable supremum, uniformly for real
Q>=2 and real starting thresholds. The source-symbol identity is retained.
-/

open scoped lp

namespace PrimeSquares

theorem selectedPage_raw_source_range {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q X : ℝ, 2 ≤ Q → 2 ≤ X →
      Real.log Q ≤ δ * Real.sqrt (Real.log X) →
      ∀ N : ℕ, X ≤ (N : ℝ) → SourcePageRawAdmissible D N Q := by
  obtain ⟨η, hη, hforce⟩ := cutoff_forcing_threshold (max 4 D.startingScale) (by omega)
  let r := (min (D.decayConstant/7) 1)/8
  have hr : 0 < r := pageDistribution_cutoff_pos D
  refine ⟨min η r, lt_min hη hr, ?_⟩
  intro Q X hQ hX hcut N hXN
  have hforceCut : Real.log Q ≤ η * Real.sqrt (Real.log X) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hBX : ((max 4 D.startingScale : ℕ) : ℝ) ≤ X := hforce Q X hQ (by linarith) hforceCut
  have hstart : D.startingScale ≤ N := by
    have hs : (D.startingScale : ℝ) ≤ (max 4 D.startingScale : ℕ) := by
      exact_mod_cast le_max_right 4 D.startingScale
    exact_mod_cast hs.trans (hBX.trans hXN)
  refine ⟨hstart, hQ, hcut.trans ?_⟩
  exact mul_le_mul (min_le_right _ _)
    (Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hXN)) (Real.sqrt_nonneg _) hr.le

theorem selectedPrimeHigh_source_bounds (HP : PrimeAsymptoticInputs) {c C : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c) (hC : 0 ≤ C)
    (hBourgain : SmoothCircleBourgainInput C) (hPage : RawPageUniquenessInput c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
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
          (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) * ‖f‖) ∧
        (∀ j, N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → ∀ ξ : ℝ,
          pageHighSymbol ((2 : ℕ)^j*2)
            (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega)
            Q (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
            (sourcePageDatum D ((2 : ℕ)^j*2) Q) (ξ : PrimeCircle) =
          paperPageHighFrequencyValue ((2 : ℕ)^j*2) Q
            (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
            (sourcePageDatum D ((2 : ℕ)^j*2) Q) ξ)) := by
  obtain ⟨δH, hδH, hHigh⟩ := proposition621_source HP hC hBourgain hc hPage
  obtain ⟨δR, hδR, hRaw⟩ := selectedPage_raw_source_range D
  let δ := min δH δR
  have hδ : 0 < δ := lt_min hδH hδR
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨K, hK, hmax⟩ := hHigh ε hε
  have hs : ∀ Q N₀ : ℝ, 2 ≤ Q → 2 ≤ N₀ → Real.log Q ≤ δ * Real.sqrt (Real.log N₀) →
      ∀ f : ℓ²(ℤ, ℂ), ∃ G : ℓ²(ℤ, ℝ),
        (∀ x, G x = ⨆ j : ℕ, ‖selectedPrimeHighTail D N₀ Q j f x‖) ∧
        (∀ x, 0 ≤ G x) ∧ (∀ j x, ‖selectedPrimeHighTail D N₀ Q j f x‖ ≤ G x) ∧
        ‖G‖ ≤ (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) * ‖f‖ ∧
        (∀ j, ‖selectedPrimeHighTail D N₀ Q j f‖ ≤
          (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) * ‖f‖) ∧
        (∀ j, N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → ∀ ξ : ℝ,
          pageHighSymbol ((2 : ℕ)^j*2)
            (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega)
            Q (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
            (sourcePageDatum D ((2 : ℕ)^j*2) Q) (ξ : PrimeCircle) =
          paperPageHighFrequencyValue ((2 : ℕ)^j*2) Q
            (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)
            (sourcePageDatum D ((2 : ℕ)^j*2) Q) ξ) := by
    intro Q N₀ hQ hN₀ hcut f
    have hcutH : Real.log Q ≤ δH * Real.sqrt (Real.log N₀) :=
      hcut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    have hcutR : Real.log Q ≤ δR * Real.sqrt (Real.log N₀) :=
      hcut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
    let E : ℕ → Option PageZeroDatum := fun j => sourcePageDatum D ((2 : ℕ)^j*2) Q
    have hE : ∀ j F, N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → E j = some F →
        (F.conductor : ℝ) ≤ sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q ∧
        1-(c/2)/Real.log (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q) < F.beta := by
      intro j F hj hF
      exact (sourcePageDatum_spec D _ Q (hRaw Q N₀ hQ hN₀ hcutR _ hj)).1 F hF
    exact hmax Q N₀ hQ hN₀ hcutH E hE f
  refine ⟨K, hK, ?_, hs⟩
  intro j Q hQ hcut hN
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hN2 : (2 : ℕ) ≤ 2^j*2 := dyadic_annular_scale_lower (M := 2) (by norm_num) j
  obtain ⟨G, _, _, _, _, hfixed, _⟩ := hs Q (((2 : ℕ)^j*2 : ℕ) : ℝ) hQ
    (by exact_mod_cast hN2) hcut f
  have h := hfixed j
  rw [selectedPrimeHighTail_of_le D _ Q j le_rfl] at h
  exact h

end PrimeSquares
