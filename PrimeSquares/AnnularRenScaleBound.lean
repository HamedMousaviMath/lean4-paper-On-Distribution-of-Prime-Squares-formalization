import PrimeSquares.AnnularRenBalancedBound
import PrimeSquares.RenScaleAbsorption

namespace PrimeSquares

noncomputable def renSourceConstant (C : ℝ) : ℝ := (C*renDivisorConstant/2)*renGeometryConstant

theorem renSourceConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ renSourceConstant C := by
  have h₁ := renDivisorConstant_pos
  have h₂ := renGeometryConstant_pos
  dsimp [renSourceConstant]
  positivity

theorem annularMangoldt_Ren_scale_bound {N : ℕ} (hN : 4 ≤ N)
    (q : ℕ) (hq : 0 < q) (ξ θ c : ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hpow : R^4 ≤ (N : ℝ)/2)
    (hql : (q : ℝ) ≤ ((N : ℝ)/2)^(1/2 : ℝ))
    (hθ : |θ| ≤ 1/((q : ℝ)*((N : ℝ)/2)^(3/2 : ℝ)))
    (hTR : R/4 ≤ renEffectiveDenominator q ((N : ℝ)/2) θ)
    (hRen : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      (C*(q.divisors.card : ℝ)^(3/2 : ℝ)*(Real.log ((N : ℝ)/2))^c)*
        renQuadraticBracket ((N : ℝ)/2) (renEffectiveDenominator q ((N : ℝ)/2) θ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      renSourceConstant C*(Real.log ((N : ℝ)/2))^c*R^(-(5/12 : ℝ)) := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log ((N : ℝ)/2) := Real.log_nonneg (by linarith)
  have hm := annularMangoldt_Ren_balanced hN q hq ξ θ c hC (by linarith) hql hθ hTR hRen
  have hb := renBalancedBudget_scale_bound hR hpow
  have hc : 0 ≤ (C*renDivisorConstant/2)*(Real.log ((N : ℝ)/2))^c := by
    have hh := renDivisorConstant_pos
    positivity
  calc
    _ ≤ (C*renDivisorConstant/2)*(Real.log ((N : ℝ)/2))^c*renBalancedBudget ((N : ℝ)/2) R := hm
    _ ≤ (C*renDivisorConstant/2)*(Real.log ((N : ℝ)/2))^c*
        (renGeometryConstant*R^(-(5/12 : ℝ))) := mul_le_mul_of_nonneg_left hb hc
    _ = _ := by dsimp [renSourceConstant];ring

end PrimeSquares
