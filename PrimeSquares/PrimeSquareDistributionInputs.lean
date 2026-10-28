import PrimeSquares.CircleApproximationData
import PrimeSquares.SourceInducedCharacters
import PrimeSquares.SourceHighOrliczUniform
import PrimeSquares.SourceScaleLowEstimate

namespace PrimeSquares

/-- Raw independent number-theoretic input. The existence of the compatible
exceptional real character, uniform progression estimate, and Ren/Ghosh
exponential-sum inputs is not proved here. In particular, this structure
assumes no high/low decomposition or improving theorem from this paper.
The conductor and character may vary with N and Q at a fixed scale. -/
structure PrimeSquareDistributionInputs where
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
  raw_data : ∀ (N : ℕ),startingScale ≤ N → ∀ Q : ℝ,2 ≤ Q →
    Real.log Q ≤ (min (decayConstant/7) 1/8)*Real.sqrt (Real.log N) →
    ∃ q₀ : ℕ,0 < q₀ ∧ ∃ χ₀ : DirichletCharacter ℂ q₀,χ₀.IsQuadratic ∧
      ∃ active : Bool,∃ β : ℝ,
        CircleAnalyticInputs N Q (sourceInducedCharacter q₀ χ₀)
          (sourceExceptionalSelector q₀ active) β progressionConstant renConstant
            ghoshConstant renPower decayConstant

/-- The permitted Q-range is genuinely nontrivial. -/
theorem distribution_cutoff_constant_pos (D : PrimeSquareDistributionInputs) :
    0 < (min (D.decayConstant/7) 1)/8 :=
  div_pos (lt_min (div_pos D.decay_pos (by norm_num)) (by norm_num)) (by norm_num)

theorem square_log_sqrt_le_double {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (Real.log (N^2)) ≤ 2*Real.sqrt (Real.log N) := by
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ Real.sqrt (4*Real.log N) := Real.sqrt_le_sqrt (by linarith)
    _ = _ := by
      rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

theorem source_low_amplitude_orlicz {N : ℕ} (hN : 1 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q) :
    2*realLowAmplitude N Q ≤
      (4*lowSpatialConstant)/((N : ℝ)^2)*Q^((1 : ℝ))*(Real.log Q)^((1 : ℝ)) := by
  have hQp : 0 < Q := by linarith
  have hl : Real.log (2*Q) ≤ 2*Real.log Q := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQp.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hQ]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*lowSpatialConstant*Q by
    exact mul_nonneg (mul_nonneg (by norm_num) lowSpatialConstant_nonneg) hQp.le)
  dsimp [realLowAmplitude]
  simp only [Real.rpow_one]
  calc
    _ = (2*lowSpatialConstant*Q*Real.log (2*Q))/(N : ℝ)^2 := by ring
    _ ≤ (2*lowSpatialConstant*Q*(2*Real.log Q))/(N : ℝ)^2 :=
      div_le_div_of_nonneg_right hm (sq_nonneg _)
    _ = _ := by ring

theorem primeSquare_orlicz_decomposition_large (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {c₁ : ℝ} (hc₁ : 2 < c₁) :
    ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∃ c₀ : ℝ,0 < c₀ ∧ ∃ CHi : ℝ,0 < CHi ∧
      ∀ N : ℕ,N₀ ≤ N → ∀ j : ℕ,2 ≤ (2 : ℝ)^j →
        Real.log ((2 : ℝ)^j) ≤ c₀*(Real.log ((N : ℝ)^2))^(1/2 : ℝ) →
        OperatorOrliczBound (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
          ((N : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 1 c₁ (1/2) 0 1 (4*lowSpatialConstant) CHi 8 := by
  obtain ⟨NLo,hNLo,hlo⟩ := sourceFullLow_uniform_source_range D.decay_pos
  obtain ⟨NErr,hNErr,herr⟩ := globalCircleApproximation_l2_operator D.progression_nonneg
    D.ren_nonneg D.ghosh_nonneg D.renPower_nonneg D.decay_pos (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨CHi,hCHi,hhi⟩ := sourceHigh_orlicz_uniform HP hc₁
  let c₀ : ℝ := ((min (D.decayConstant/7) 1)/8)/2
  refine ⟨max D.startingScale (max NLo NErr),?_,c₀,
    div_pos (distribution_cutoff_constant_pos D) (by norm_num),CHi,hCHi,?_⟩
  · exact hNLo.trans ((le_max_left _ _).trans (le_max_right _ _))
  intro N hn j hj hcut
  have hnLo : NLo ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnErr : NErr ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnD : D.startingScale ≤ N := (le_max_left _ _).trans hn
  have hN4 : 4 ≤ N := hNLo.trans hnLo
  have hN : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ : 0 < (2 : ℝ)^j := by positivity
  have hraw : Real.log ((2 : ℝ)^j) ≤ ((min (D.decayConstant/7) 1)/8)*Real.sqrt (Real.log N) := by
    rw [←Real.sqrt_eq_rpow] at hcut
    exact hcut.trans (by
      have hm := mul_le_mul_of_nonneg_left (square_log_sqrt_le_double hNr)
        (show 0 ≤ c₀ from (div_pos (distribution_cutoff_constant_pos D) (by norm_num)).le)
      dsimp [c₀] at hm ⊢
      nlinarith)
  obtain ⟨q₀,hq₀,χ₀,hχ,active,β,hi⟩ := D.raw_data N hnD ((2 : ℝ)^j) hj hraw
  have : NeZero q₀ := ⟨hq₀.ne'⟩
  let Γ := sourceRationalCenters (sourceMajorArcScale N ((2 : ℝ)^j))
  have hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊sourceMajorArcScale N ((2 : ℝ)^j)⌋₊ := by
    intro r hr
    exact (mem_canonicalRationalCenters _ r).mp hr
  let Lo := circleLowOperator Γ N hN q₀ ((2 : ℝ)^j) (conductorMajorant q₀)
    (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β
  let Hi := circleHighOperator Γ N hN q₀ ((2 : ℝ)^j) (conductorMajorant q₀)
    (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β
  let Err := circleMajorArcErrorOperator Γ N hN (sourceInducedCharacter q₀ χ₀)
    (sourceExceptionalSelector q₀ active) β
  have hLo : ‖Lo‖ ≤ (4*lowSpatialConstant)/((N : ℝ)^2)*((2 : ℝ)^j)^((1 : ℝ))*
      (Real.log ((2 : ℝ)^j))^((1 : ℝ)) :=
    (hlo N hnLo ((2 : ℝ)^j) hj hraw q₀ χ₀ hχ active β hi.beta_le_one hN).1.trans
      (source_low_amplitude_orlicz hN hj)
  have hHi := (hhi N (by omega) j hj q₀ χ₀ hχ _ Γ hΓ active β hi.beta_pos.le hi.beta_le_one).2
  have hErr := herr N hnErr ((2 : ℝ)^j) (by linarith) hraw (sourceInducedCharacter q₀ χ₀)
    (sourceExceptionalSelector q₀ active) β hi hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hscale : (1+Real.log N)^(-(1 : ℝ)) ≤ 2*(1+Real.log ((N : ℝ)^2))^(-(1 : ℝ)) := by
    rw [Real.rpow_neg_one,Real.rpow_neg_one,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ)*(1+2*Real.log (N : ℝ))⁻¹=2/(1+2*Real.log (N : ℝ)) by ring,←one_div]
    exact (div_le_div_iff₀ (by linarith : 0 < 1+Real.log (N : ℝ))
      (by linarith : 0 < 1+2*Real.log (N : ℝ))).mpr (by linarith)
  have he : ‖Err‖ ≤ 8*((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^((0 : ℝ))*
      (1+Real.log ((N : ℝ)^2))^(-(1 : ℝ)) := by
    simp only [Real.rpow_zero,mul_one]
    calc
      _ ≤ 2*((2 : ℝ)^(1 : ℝ)*((2 : ℝ)^j)^(-(1/2 : ℝ))*(1+Real.log N)^(-(1 : ℝ))) := hErr
      _ = (4*((2 : ℝ)^j)^(-(1/2 : ℝ)))*(1+Real.log N)^(-(1 : ℝ)) := by rw [Real.rpow_one];ring
      _ ≤ (4*((2 : ℝ)^j)^(-(1/2 : ℝ)))*(2*(1+Real.log ((N : ℝ)^2))^(-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  refine ⟨Lo,Hi,Err,?_,?_,?_,?_⟩
  · intro F x
    have hs := annularKernel_finite_low_high_error Γ N hN q₀ ((2 : ℝ)^j) (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β F (fun _ => 1) x
    simpa only [finiteConvolution_indicator,finiteInputLp_one] using hs
  · intro f
    exact (Lo.le_opNorm f).trans (mul_le_mul_of_nonneg_right hLo (norm_nonneg _))
  · intro f
    exact (Hi.le_opNorm f).trans (mul_le_mul_of_nonneg_right hHi (norm_nonneg _))
  · intro f
    exact (Err.le_opNorm f).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))

end PrimeSquares
