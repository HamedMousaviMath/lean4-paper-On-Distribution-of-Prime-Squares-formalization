import PrimeSquares.RenBalancedBracket

namespace PrimeSquares

theorem renQuadraticBracket_nonneg {x T : ℝ} (hx : 0 ≤ x) (_hT : 0 ≤ T) :
    0 ≤ renQuadraticBracket x T := by
  dsimp [renQuadraticBracket]
  positivity

theorem annularMangoldt_Ren_balanced {N : ℕ} (hN : 4 ≤ N)
    (q : ℕ) (hq : 0 < q) (ξ θ c : ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hql : (q : ℝ) ≤ ((N : ℝ)/2)^(1/2 : ℝ))
    (hθ : |θ| ≤ 1/((q : ℝ)*((N : ℝ)/2)^(3/2 : ℝ)))
    (hTR : R/4 ≤ renEffectiveDenominator q ((N : ℝ)/2) θ)
    (hRen : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      (C*(q.divisors.card : ℝ)^(3/2 : ℝ)*(Real.log ((N : ℝ)/2))^c)*
        renQuadraticBracket ((N : ℝ)/2) (renEffectiveDenominator q ((N : ℝ)/2) θ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      (C*renDivisorConstant/2)*(Real.log ((N : ℝ)/2))^c*renBalancedBudget ((N : ℝ)/2) R := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hx : (0 : ℝ) < (N : ℝ)/2 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ)/2) := Real.log_nonneg (by linarith)
  have hTp : 0 < renEffectiveDenominator q ((N : ℝ)/2) θ :=
    (by positivity : 0 < R/4).trans_le hTR
  have hb := renQuadraticBracket_nonneg hx.le hTp.le
  have hd := ren_divisor_prefactor_bound q hq
  have hw := ren_weighted_bracket_from_balanced_approximation hx hR q hq hql hθ hTR
  calc
    _ ≤ (C*(q.divisors.card : ℝ)^(3/2 : ℝ)*(Real.log ((N : ℝ)/2))^c)*
        renQuadraticBracket ((N : ℝ)/2) (renEffectiveDenominator q ((N : ℝ)/2) θ)/N :=
      annularMangoldt_from_Ren_bound N ξ _ _ hRen
    _ ≤ (C*(renDivisorConstant*(q : ℝ)^(1/12 : ℝ))*(Real.log ((N : ℝ)/2))^c)*
        renQuadraticBracket ((N : ℝ)/2) (renEffectiveDenominator q ((N : ℝ)/2) θ)/N := by gcongr
    _ = (C*renDivisorConstant/2)*(Real.log ((N : ℝ)/2))^c*
        ((q : ℝ)^(1/12 : ℝ)*renQuadraticBracket ((N : ℝ)/2)
          (renEffectiveDenominator q ((N : ℝ)/2) θ)/((N : ℝ)/2)) := by
      field_simp [hnp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by have hp := renDivisorConstant_pos;positivity)

end PrimeSquares
