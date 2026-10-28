import PrimeSquares.CircleHighPowerSymbolBound
import PrimeSquares.CircleHighLowNormInputs

namespace PrimeSquares

theorem highPowerConstant_nonneg {C T δ η : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hδη : η < δ) :
    0 ≤ highPowerConstant C T δ η := by
  have hK : 0 < highMaskConstant := (by norm_num : (0 : ℝ) < 1).trans_le highMaskConstant_one_le
  have hd := geometric_inverse_power_denominator_pos (sub_pos.mpr hδη)
  unfold highPowerConstant
  positivity

theorem circleHighOperator_power_bound {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ) (M q₀ : ℕ) [NeZero q₀]
    {Q C T δ η : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hT : 0 ≤ T) (hδη : η < δ)
    (hratio : conductorMajorant q₀/(q₀ : ℝ) ≤ T) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hG : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q),IsUnit a →
      ‖principalSquareSum q a‖ ≤ C*(q : ℝ)^(-δ) ∧ ‖twistedSquareSum q χ a‖ ≤ C*(q : ℝ)^(-δ))
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hk : ∀ r ∈ Γ,‖κ r‖ ≤ 1) :
    ‖circleHighOperator Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β‖ ≤ highPowerConstant C T δ η*Q^(-η) := by
  apply circleHighOperator_symbol_bound
  · exact mul_nonneg (highPowerConstant_nonneg hC hT hδη) (Real.rpow_nonneg hQ.le _)
  · exact circleHighModel_power_bound hN Γ M q₀ hQ hC hT hδη hratio hη0 hη1 hG hΓ χ κ hβ0 hβ1 hk

end PrimeSquares
