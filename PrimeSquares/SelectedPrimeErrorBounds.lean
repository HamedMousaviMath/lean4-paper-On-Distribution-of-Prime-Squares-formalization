import PrimeSquares.FinitePageErrorBound

/-!
# Every error exponent with one fixed source range and operator family

The large-scale approximation is combined with the elementary finite-scale
envelope. Thus the cutoff coefficient is chosen before A, and the operator
does not change with A. The proved logarithmic Q power is zero, which is
stronger than the source's permitted polynomial logarithmic factor.
-/

open scoped lp

namespace PrimeSquares

theorem selectedPrimeError_all_exponents {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, 0 ≤ A → ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
      Real.log Q ≤ δ * Real.sqrt (Real.log N) → SourcePageRawAdmissible D N Q →
      ∀ hN : 1 ≤ N, ‖selectedPrimeError D N hN Q‖ ≤
        K * Q^(-(1/2 : ℝ)) * (1 + Real.log N)^(-A) := by
  obtain ⟨δG, hδG, hGeom⟩ := sourceHigh_uniform_geometry
  let r := (min (D.decayConstant/7) 1)/8
  have hr : 0 < r := pageDistribution_cutoff_pos D
  let δ := min δG r
  refine ⟨δ, lt_min hδG hr, ?_⟩
  intro A hA
  obtain ⟨T, hT, hError⟩ := globalCircleApproximation_l2_operator D.progression_nonneg
    D.ren_nonneg D.ghosh_nonneg D.renPower_nonneg D.decay_pos hA
  let B := finitePageErrorEnvelope T
  have hB : 0 < B := finitePageErrorEnvelope_pos T
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  let L := 1 + Real.log (T : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hTr]
  let K := 1 + 2*(2 : ℝ)^A + B*(T : ℝ)^(1/2 : ℝ)*L^A
  have hK : 0 < K := by dsimp [K]; positivity
  have hKL : 2*(2 : ℝ)^A ≤ K := by
    have hs : 0 ≤ B*(T : ℝ)^(1/2 : ℝ)*L^A := by positivity
    dsimp [K]
    linarith
  have hKS : B*(T : ℝ)^(1/2 : ℝ)*L^A ≤ K := by
    dsimp [K]
    have hp : 0 < (2 : ℝ)^A := Real.rpow_pos_of_pos (by norm_num) A
    linarith
  refine ⟨K, hK, ?_⟩
  intro N hn Q hQ hcut hRaw hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hn
  have hQp : 0 < Q := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have hX : 0 < 1 + Real.log (N : ℝ) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)]
  have hcutG : Real.log Q ≤ δG * Real.sqrt (Real.log N) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hcutR : Real.log Q ≤ r * Real.sqrt (Real.log N) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  have hb : 2*(sourceMajorArcScale N Q)^8 ≤ (N : ℝ)^2 :=
    hGeom Q N hQ hNr hcutG N le_rfl
  by_cases hlarge : T ≤ N
  · have hraw := (sourcePageDatum_spec D N Q hRaw).2
    have he := hError N hlarge Q (by linarith) hcutR _ _ _ hraw hN
    calc
      ‖selectedPrimeError D N hN Q‖ ≤
          2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := he
      _ = (2*(2 : ℝ)^A)*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKL (by positivity)) (by positivity)
  · have hNT : N ≤ T := (lt_of_not_ge hlarge).le
    have hfinite : ‖selectedPrimeError D N hN Q‖ ≤ B :=
      finitePageError_bound hn hNT hQ hb (sourcePageDatum D N Q)
    have hQT : Q ≤ (T : ℝ) :=
      (sourceMajorArcScale_cutoff_le (by linarith : 1 ≤ Q) N).trans
        ((sourceRadius_le_scale hQ hb).trans (by exact_mod_cast hNT))
    have hlogT : 1 + Real.log (N : ℝ) ≤ L := by
      dsimp [L]
      linarith [Real.log_le_log hNp (show (N : ℝ) ≤ T by exact_mod_cast hNT)]
    have hcoef : B*Q^(1/2 : ℝ)*(1+Real.log N)^A ≤ K :=
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hQp.le hQT (by norm_num)) hB.le)
        (Real.rpow_le_rpow hX.le hlogT hA) (by positivity) (by positivity)).trans hKS
    have hQc : Q^(1/2 : ℝ)*Q^(-(1/2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hQp]
      norm_num
    have hXc : (1+Real.log (N : ℝ))^A*(1+Real.log (N : ℝ))^(-A) = 1 := by
      rw [← Real.rpow_add hX]
      simp
    have hundo : B = (B*Q^(1/2 : ℝ)*(1+Real.log N)^A)*
        Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
      calc
        B = B*(Q^(1/2 : ℝ)*Q^(-(1/2 : ℝ)))*
            ((1+Real.log (N : ℝ))^A*(1+Real.log (N : ℝ))^(-A)) := by
          rw [hQc, hXc, mul_one, mul_one]
        _ = _ := by ring
    exact hfinite.trans (hundo.trans_le (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)))

end PrimeSquares
