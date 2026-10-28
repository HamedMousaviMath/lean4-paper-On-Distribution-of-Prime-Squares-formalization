import PrimeSquares.SelectedPrimeSquareOperators
import PrimeSquares.SourceLocalMass

/-!
# Uniform source range and both low-term estimates

A small fixed cutoff constant absorbs any fixed starting threshold. The
choice here is independent of every high epsilon and error exponent.
-/

open scoped lp

namespace PrimeSquares

theorem cutoff_forcing_threshold (B : ℕ) (hB : 1 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q X : ℝ, 2 ≤ Q → 1 ≤ X →
      Real.log Q ≤ δ * Real.sqrt (Real.log X) → (B : ℝ) ≤ X := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBr
  let L := Real.log (B : ℝ) + 1
  have hL : 0 < L := by dsimp [L]; linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ := Real.log 2 / (2 * Real.sqrt L)
  have hδ : 0 < δ := div_pos hlog2 (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro Q X hQ hX hcut
  by_contra hBX
  have hXB : X ≤ (B : ℝ) := (lt_of_not_ge hBX).le
  have hLog : Real.log X ≤ L :=
    (Real.log_le_log (by linarith) hXB).trans (by dsimp [L]; linarith)
  have hb : Real.log 2 ≤ δ * Real.sqrt L :=
    ((Real.log_le_log (by norm_num) hQ).trans hcut).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLog) hδ.le)
  have he : δ * Real.sqrt L = Real.log 2 / 2 := by
    dsimp [δ]
    field_simp [hsL.ne']
  rw [he] at hb
  linarith

theorem selectedPrimeLow_source_bounds :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {c : ℝ} (D : PagePrimeSquareDistributionInputs c),
    ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
      Real.log Q ≤ δ * Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
      ‖selectedPrimeLow D N hN Q‖ ≤
        (2 * lowSpatialConstant) * ((N : ℝ)^2)⁻¹ * Q * Real.log (2*Q) ∧
      ∀ (f : ℓ¹(ℤ, ℂ)) (x : ℤ),
        ‖selectedPrimeLow D N hN Q f x‖ ≤
          (8 * lowSpatialConstant * Q * Real.log (2*Q)) * sourceLocalMass N f x := by
  obtain ⟨NLo, hNLo, hlo⟩ := sourceFullLow_uniform_source_range (c := 7) (by norm_num)
  obtain ⟨δ, hδ, hforce⟩ := cutoff_forcing_threshold NLo (by omega)
  refine ⟨min δ (1/8), lt_min hδ (by norm_num), ?_⟩
  intro c D N hn Q hQ hcut hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hforceCut : Real.log Q ≤ δ * Real.sqrt (Real.log N) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hnLo : NLo ≤ N := by exact_mod_cast hforce Q N hQ hNr hforceCut
  have hraw : Real.log Q ≤ (min ((7 : ℝ)/7) 1/8) * Real.sqrt (Real.log N) := by
    rw [show (min ((7 : ℝ)/7) 1/8) = (1/8 : ℝ) by norm_num]
    exact hcut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  let E := sourcePageDatum D N Q
  have : NeZero (optionPageConductor 1 E) := ⟨(optionPageConductor_pos E).ne'⟩
  have hb := hlo N hnLo Q hQ hraw (optionPageConductor 1 E) (optionPageCharacter 1 E)
    (optionPageCharacter_quadratic E) E.isSome (optionPageBeta E) (optionPageBeta_le_one E) hN
  refine ⟨?_, ?_⟩
  · change ‖fourierL1Operator _‖ ≤ _
    exact hb.1.trans_eq (by dsimp [realLowAmplitude]; ring)
  · intro f x
    have hlog : 0 ≤ Real.log (2*Q) := Real.log_nonneg (by linarith)
    have hA : 0 ≤ 8 * lowSpatialConstant * Q * Real.log (2*Q) := by
      have hl := lowSpatialConstant_nonneg
      positivity
    exact fourierL1Operator_local_of_finite (selectedPrimeLowSymbol D N hN Q) hN hA hb.2 f x

end PrimeSquares
