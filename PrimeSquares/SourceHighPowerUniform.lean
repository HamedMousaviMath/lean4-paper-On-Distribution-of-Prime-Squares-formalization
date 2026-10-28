import PrimeSquares.CircleHighL2PowerBound

namespace PrimeSquares

theorem sourceHigh_power_uniform {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (Q : ℝ),0 < Q →
    ∀ (q₀ : ℕ) [NeZero q₀] (M : ℕ) (Γ : Finset ℚ),
      (∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M) →
    ∀ (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),0 ≤ β → β ≤ 1 →
      (∀ r ∈ Γ,‖κ r‖ ≤ 1) →
      (∀ θ,‖circleHighModel Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β θ‖ ≤ H*Q^(-η)) ∧
      ‖circleHighOperator Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β‖ ≤ H*Q^(-η) := by
  let δ : ℝ := (η+1/2)/2
  have hδη : η < δ := by dsimp [δ];linarith
  have hδhalf : δ < 1/2 := by dsimp [δ];linarith
  obtain ⟨C,hC,hG⟩ := gauss_pair_arbitrary_decay hδhalf
  obtain ⟨T,hT,hratio⟩ := conductorMajorant_ratio_uniform
  have hK : 0 < highMaskConstant := (by norm_num : (0 : ℝ) < 1).trans_le highMaskConstant_one_le
  have hH : 0 < highPowerConstant C T δ η := by
    have hd := geometric_inverse_power_denominator_pos (sub_pos.mpr hδη)
    unfold highPowerConstant
    positivity
  refine ⟨highPowerConstant C T δ η,hH,?_⟩
  intro N hN Q hQ q₀ inst M Γ hΓ χ κ β hβ0 hβ1 hk
  have hr := hratio q₀ (NeZero.pos q₀)
  have hη1 : η ≤ 1 := by linarith
  exact ⟨circleHighModel_power_bound hN Γ M q₀ hQ hC.le hT.le hδη hr hη0.le hη1 hG hΓ χ κ hβ0 hβ1 hk,
    circleHighOperator_power_bound hN Γ M q₀ hQ hC.le hT.le hδη hr hη0.le hη1 hG hΓ χ κ hβ0 hβ1 hk⟩

end PrimeSquares
