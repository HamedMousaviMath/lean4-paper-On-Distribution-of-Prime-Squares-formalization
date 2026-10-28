import PrimeSquares.SourceHighThresholdUniform
import PrimeSquares.SourceHighPowerUniform
import PrimeSquares.OrliczPairing

open Filter Topology
namespace PrimeSquares

theorem log_four_one_le : (1 : ℝ) ≤ Real.log 4 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
  rw [show (1/2 : ℝ)=(2 : ℝ)⁻¹ by norm_num,Real.log_inv] at h
  have he : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.log_pow];norm_num
  linarith

theorem orliczHighFactor_one_le {c₁ Q : ℝ} (hc₁ : 0 ≤ c₁) (hQ : 4 ≤ Q) :
    1 ≤ orliczHighFactor c₁ (1/2) Q := by
  have hl : 1 ≤ Real.log Q := log_four_one_le.trans
    (Real.log_le_log (by norm_num) hQ)
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (by linarith) _)) (Real.log_nonneg hl)

theorem gaussAnalyticMajorant_unregularized_eventually (H : PrimeAsymptoticInputs)
    {c₁ : ℝ} (hc₁ : 2 < c₁) :
    ∀ᶠ y : ℝ in atTop,gaussAnalyticMajorant y ≤ c₁*gaussAsymptoticScale y := by
  have h := (gaussAnalyticMajorant_ratio_tendsto H).eventually
    (eventually_lt_nhds hc₁)
  filter_upwards [h,eventually_ge_atTop (2 : ℝ)] with y hy h2
  exact (div_le_iff₀ (gaussAsymptoticScale_pos (by linarith))).mp hy.le

theorem sourceHigh_orlicz_uniform (H : PrimeAsymptoticInputs) {c₁ : ℝ} (hc₁ : 2 < c₁) :
    ∃ D : ℝ,0 < D ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (j : ℕ),2 ≤ (2 : ℝ)^j →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ (M : ℕ) (Γ : Finset ℚ),(∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M) →
    ∀ (active : Bool) (β : ℝ),0 ≤ β → β ≤ 1 →
      (∀ θ,‖circleHighModel Γ N (by omega) q₀ ((2 : ℝ)^j) (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β θ‖ ≤
          D*((2 : ℝ)^j)^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) ((2 : ℝ)^j)) ∧
      ‖circleHighOperator Γ N (by omega) q₀ ((2 : ℝ)^j) (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β‖ ≤
          D*((2 : ℝ)^j)^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) ((2 : ℝ)^j) := by
  obtain ⟨H₁,hH₁,ht⟩ := sourceHigh_threshold_uniform
  obtain ⟨H₂,hH₂,hp⟩ := sourceHigh_power_uniform (by norm_num : (0 : ℝ) < 1/4) (by norm_num)
  obtain ⟨Y,hY⟩ := ((gaussAnalyticMajorant_unregularized_eventually H hc₁).and
    gaussThresholdSlope_eventually_quarter).exists_forall_of_atTop
  let L : ℝ := max 2 Y
  let T : ℝ := Real.exp L
  have hT : 0 < T := Real.exp_pos _
  let Z : ℝ := (2 : ℝ)^(1/4 : ℝ)/orliczHighFactor c₁ (1/2) 2
  have hZ : 0 < Z := div_pos (by positivity) (Real.exp_pos _)
  let D : ℝ := 1+H₁+H₂*T^(1/4 : ℝ)+H₂*Z
  have hD : 0 < D := by dsimp [D];positivity
  have ht0 : 0 ≤ H₂*T^(1/4 : ℝ) := by positivity
  have hz0 : 0 ≤ H₂*Z := by positivity
  have hD₁ : H₁ ≤ D := by dsimp [D];linarith
  have hD₂ : H₂*T^(1/4 : ℝ) ≤ D := by dsimp [D];linarith
  have hDZ : H₂*Z ≤ D := by dsimp [D];linarith
  refine ⟨D,hD,?_⟩
  intro N hN j hj q₀ inst χ₀ hχ M Γ hΓ active β hβ0 hβ1
  let Q : ℝ := (2 : ℝ)^j
  have hQ : 0 < Q := by dsimp [Q];positivity
  have hpower := hp N hN Q hQ q₀ M Γ hΓ (sourceInducedCharacter q₀ χ₀)
    (sourceExceptionalSelector q₀ active) β hβ0 hβ1
    (fun r _ => sourceExceptionalSelector_norm q₀ active r)
  have hid : Q^(-(1/4 : ℝ))=Q^(1/4 : ℝ)*Q^(-(1/2 : ℝ)) := by
    rw [←Real.rpow_add hQ];norm_num
  by_cases hl : L ≤ Real.log Q
  · have hy := hY (Real.log Q) ((le_max_right _ _).trans hl)
    have hL : 2 ≤ Real.log Q := (le_max_left _ _).trans hl
    have he : Real.exp (gaussAnalyticMajorant (Real.log Q)) ≤ orliczHighFactor c₁ (1/2) Q := by
      apply Real.exp_le_exp.mpr
      simpa only [gaussAsymptoticScale,orliczHighFactor,Real.sqrt_eq_rpow,mul_div_assoc] using hy.1
    have hb := ht N hN Q hQ hL hy.2.2 q₀ χ₀ hχ M Γ hΓ active β hβ0 hβ1
    have hscalar : H₁*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)) ≤
        D*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right hD₁ (by positivity)) he (Real.exp_pos _).le (by positivity)
    exact ⟨fun θ => (hb.1 θ).trans hscalar,hb.2.trans hscalar⟩
  · have hQT : Q ≤ T := by
      dsimp [T]
      exact (Real.log_le_iff_le_exp hQ).mp (le_of_not_ge hl)
    have hscalar : H₂*Q^(-(1/4 : ℝ)) ≤ D*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q := by
      rw [hid]
      by_cases hj1 : j=1
      · have heQ : Q=2 := by simp only [Q,hj1,pow_one]
        rw [heQ]
        have he : H₂*((2 : ℝ)^(1/4 : ℝ))=
            (H₂*Z)*orliczHighFactor c₁ (1/2) 2 := by
          dsimp [Z]
          have hf : orliczHighFactor c₁ (1/2) 2 ≠ 0 := (Real.exp_pos _).ne'
          field_simp [hf]
        calc
          _ = (H₂*((2 : ℝ)^(1/4 : ℝ)))*((2 : ℝ)^(-(1/2 : ℝ))) := by ring
          _ = ((H₂*Z)*orliczHighFactor c₁ (1/2) 2)*((2 : ℝ)^(-(1/2 : ℝ))) := by rw [he]
          _ ≤ (D*orliczHighFactor c₁ (1/2) 2)*((2 : ℝ)^(-(1/2 : ℝ))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDZ (Real.exp_pos _).le) (by positivity)
          _ = _ := by ring
      · have hj2 : 2 ≤ j := by
          have hj0 : j ≠ 0 := by
            intro hz
            rw [hz,pow_zero] at hj
            norm_num at hj
          omega
        have h4 : 4 ≤ Q := by
          change 4 ≤ (2 : ℝ)^j
          exact (by norm_num : (4 : ℝ) ≤ 2^2).trans (pow_le_pow_right₀ (by norm_num) hj2)
        have he := orliczHighFactor_one_le (by linarith : 0 ≤ c₁) h4
        have hc : H₂*Q^(1/4 : ℝ) ≤ D :=
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hQ.le hQT (by norm_num)) hH₂.le).trans hD₂
        calc
          _ = (H₂*Q^(1/4 : ℝ))*Q^(-(1/2 : ℝ)) := by ring
          _ ≤ D*Q^(-(1/2 : ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) he
    exact ⟨fun θ => (hpower.1 θ).trans hscalar,hpower.2.trans hscalar⟩

end PrimeSquares
