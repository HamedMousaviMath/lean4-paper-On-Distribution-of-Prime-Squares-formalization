import PrimeSquares.RenBalancedBracket
import PrimeSquares.SourceScaleFourthPower

namespace PrimeSquares

noncomputable def renGeometryConstant : ℝ := Real.sqrt 2+1+(4 : ℝ)^(5/12 : ℝ)

theorem renGeometryConstant_pos : 0 < renGeometryConstant := by
  dsimp [renGeometryConstant]
  positivity

theorem renBalancedBudget_scale_bound {x R : ℝ} (hR : 1 ≤ R) (hpow : R^4 ≤ x) :
    renBalancedBudget x R ≤ renGeometryConstant*R^(-(5/12 : ℝ)) := by
  have hRp : 0 < R := by linarith
  have h₁ := inverse_rpow_from_fourth_power hRp (by norm_num : (0 : ℝ) ≤ 5/24) hpow
  have h₂ := inverse_rpow_from_fourth_power hRp (by norm_num : (0 : ℝ) ≤ 19/120) hpow
  norm_num at h₁ h₂
  have he₁ : R^(-(5/6 : ℝ)) ≤ R^(-(5/12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have he₂ : R^(-(19/30 : ℝ)) ≤ R^(-(5/12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hmul := mul_le_mul_of_nonneg_left (h₁.trans he₁) hs
  dsimp [renBalancedBudget,renGeometryConstant]
  nlinarith only [hmul,h₂.trans he₂]

theorem renBalancedBudget_quarter_bound {x R : ℝ} (hR : 1 ≤ R) (hpow : R^4 ≤ x) :
    renBalancedBudget x R ≤ renGeometryConstant*R^(-(1/4 : ℝ)) :=
  (renBalancedBudget_scale_bound hR hpow).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : -(5/12 : ℝ) ≤ -(1/4 : ℝ)))
      renGeometryConstant_pos.le)

end PrimeSquares
