import PrimeSquares.CenteredHighThresholdProfile
import PrimeSquares.CircleHighFiniteWindow
import PrimeSquares.CircleHighLowNormInputs

open Finset
namespace PrimeSquares

theorem sourceHigh_threshold_uniform :
    ∃ H : ℝ,0 < H ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (Q : ℝ),0 < Q →
      2 ≤ Real.log Q → gaussThresholdSlope (Real.log Q) ≤ 1/4 →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ (M : ℕ) (Γ : Finset ℚ),(∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M) →
    ∀ (active : Bool) (β : ℝ),0 ≤ β → β ≤ 1 →
      (∀ θ,‖circleHighModel Γ N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β θ‖ ≤
          H*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q))) ∧
      ‖circleHighOperator Γ N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β‖ ≤
          H*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)) := by
  obtain ⟨S,hS,hσ⟩ := conductorSigma_majorant_uniform
  let I : ℝ := interpolationWeightConstant ((2 : ℝ)^(1/4 : ℝ)) 1 (1/4) (1/4)
  have hI : 0 ≤ I := interpolationWeightConstant_nonneg (by positivity) (by norm_num) (by norm_num) (by norm_num)
  have hK : 0 ≤ highMaskConstant := (by norm_num : (0 : ℝ) ≤ 1).trans highMaskConstant_one_le
  let H : ℝ := 1+12*(4*highMaskConstant+32*highMaskConstant*S)*I
  have hH : 0 < H := by dsimp [H];positivity
  refine ⟨H,hH,?_⟩
  intro N hN Q hQ hL hSlope q₀ inst χ₀ hχ M Γ hΓ active β hβ0 hβ1
  have hBp : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  have hq₀ : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  let T : ℝ := Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q))
  have hT : 0 ≤ T := by dsimp [T];positivity
  have hsum : ∀ ξ : ℝ,‖∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r (ξ-(r : ℝ))‖ ≤
        4*((4*highMaskConstant*T)+(32*highMaskConstant*S*T))*I := by
    intro ξ
    apply rational_two_relative_cutoff_sum Γ M ξ _ (by norm_num : (0 : ℝ) < 1/4)
      hQ (div_pos (mul_pos hQ hq₀) hBp) (by positivity) (by positivity) hΓ
    · intro r _ hz
      exact centeredHighSymbol_zero_of_broad N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r _ hz
    · intro r _
      simpa only [T,mul_assoc] using centeredHighSymbol_threshold_profile hN q₀ χ₀ hχ active
        hQ hS.le (hσ q₀ χ₀) hL hSlope hβ0 hβ1 r (ξ-(r : ℝ))
  have hmodel : ∀ θ,‖circleHighModel Γ N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β θ‖ ≤ H*T := by
    apply circleBound_from_fundamental_interval
    intro ξ hξ
    rw [circleHighModel_finite_window Γ N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β
      (fun r hr => (hΓ r hr).1) hξ]
    have h1 := hsum (ξ-1)
    have h2 := hsum ξ
    have h3 := hsum (ξ+1)
    have hn := (norm_add_le
      ((∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r (ξ-1-(r : ℝ)))+
       ∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r (ξ-(r : ℝ)))
      (∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀)
        (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r (ξ+1-(r : ℝ)))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    exact hn.trans (by dsimp [H];nlinarith)
  refine ⟨?_,?_⟩
  · simpa only [T,mul_assoc] using hmodel
  · have hbound := circleHighOperator_symbol_bound Γ N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β (mul_nonneg hH.le hT) hmodel
    simpa only [T,mul_assoc] using hbound

end PrimeSquares
