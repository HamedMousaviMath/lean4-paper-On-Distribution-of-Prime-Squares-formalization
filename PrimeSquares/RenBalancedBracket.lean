import PrimeSquares.RenInverseEffectiveTerm

namespace PrimeSquares

noncomputable def renBalancedBudget (x R : ℝ) : ℝ :=
  Real.sqrt 2*x^(-(5/24 : ℝ)) + x^(-(19/120 : ℝ)) +
    (4 : ℝ)^(5/12 : ℝ)*R^(-(5/12 : ℝ))

theorem renBalancedBudget_nonneg {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    0 ≤ renBalancedBudget x R := by
  dsimp [renBalancedBudget]
  positivity

theorem ren_weighted_bracket_balanced {x q T R : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hR : 0 < R) (hql : q ≤ x^(1/2 : ℝ)) (hqu : T ≤ 2*x^(1/2 : ℝ))
    (hqT : q ≤ T) (hTR : R/4 ≤ T) :
    q^(1/12 : ℝ)*renQuadraticBracket x T/x ≤ renBalancedBudget x R := by
  have h₁ := ren_first_weighted_term hx hq hql hqu
  have h₂ := ren_middle_weighted_term hx hq hql
  have h₃ := ren_third_weighted_term hx hq hR hqT hTR
  calc
    _ = q^(1/12 : ℝ)*(Real.sqrt x*Real.sqrt T)/x +
        q^(1/12 : ℝ)*x^(4/5 : ℝ)/x + q^(1/12 : ℝ)*(x/Real.sqrt T)/x := by
      dsimp [renQuadraticBracket]
      ring
    _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃

theorem ren_weighted_bracket_from_balanced_approximation {x θ R : ℝ}
    (hx : 0 < x) (hR : 0 < R) (q : ℕ) (hq : 0 < q)
    (hql : (q : ℝ) ≤ x^(1/2 : ℝ))
    (hθ : |θ| ≤ 1/((q : ℝ)*x^(3/2 : ℝ)))
    (hTR : R/4 ≤ renEffectiveDenominator q x θ) :
    (q : ℝ)^(1/12 : ℝ)*renQuadraticBracket x (renEffectiveDenominator q x θ)/x ≤
      renBalancedBudget x R :=
  ren_weighted_bracket_balanced hx (Nat.cast_nonneg q) hR hql
    (renEffectiveDenominator_balanced_upper hx q hq hql hθ)
    (renEffectiveDenominator_ge q x θ) hTR

end PrimeSquares
