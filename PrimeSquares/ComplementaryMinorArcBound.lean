import PrimeSquares.AnnularRenScaleBound
import PrimeSquares.GhoshScaleAbsorption
import PrimeSquares.OutsideSourceArcs
import PrimeSquares.BalancedRationalApproximation

namespace PrimeSquares

def RenBalancedInput (N : ℕ) (ξ C c : ℝ) : Prop :=
  ∀ r : ℚ, (r.den : ℝ) ≤ ((N : ℝ)/2)^(1/2 : ℝ) →
    |ξ-(r : ℝ)| ≤ 1/((r.den : ℝ)*((N : ℝ)/2)^(3/2 : ℝ)) →
    ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      (C*(r.den.divisors.card : ℝ)^(3/2 : ℝ)*(Real.log ((N : ℝ)/2))^c)*
        renQuadraticBracket ((N : ℝ)/2)
          (renEffectiveDenominator r.den ((N : ℝ)/2) (ξ-(r : ℝ)))

def GhoshBalancedInput (N : ℕ) (ξ B : ℝ) : Prop :=
  ∀ r : ℚ, ((N : ℝ)/2)^(1/2 : ℝ) ≤ (r.den : ℝ) →
    (r.den : ℝ) ≤ ((N : ℝ)/2)^(3/2 : ℝ) → |ξ-(r : ℝ)| < 1/(r.den : ℝ)^2 →
    ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤ B*((N : ℝ)/2)^(17/16 : ℝ)*
      (ghoshQuadraticBracket ((N : ℝ)/2) r.den)^(1/4 : ℝ)

noncomputable def complementaryMinorBudget (N : ℕ) (C B c R : ℝ) : ℝ :=
  renSourceConstant C*(Real.log ((N : ℝ)/2))^c*R^(-(5/12 : ℝ)) +
    ghoshSourceConstant B*R^(-(1/4 : ℝ))

theorem complementaryMinorBudget_nonneg {N : ℕ} (hN : 2 ≤ N)
    {C B R : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) (c : ℝ) :
    0 ≤ complementaryMinorBudget N C B c R := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log ((N : ℝ)/2) := Real.log_nonneg (by linarith)
  have hc := renSourceConstant_nonneg hC
  have hb := ghoshSourceConstant_nonneg hB
  dsimp [complementaryMinorBudget]
  positivity

theorem annularMangoldt_complementary_minor_bound {N : ℕ} (hN : 4 ≤ N)
    {C B c R ξ : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hpow : R^4 ≤ (N : ℝ)/2) (hout : OutsideSourceMajorArcs N R ξ)
    (hRen : RenBalancedInput N ξ C c) (hGhosh : GhoshBalancedInput N ξ B) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      complementaryMinorBudget N C B c R := by
  obtain ⟨r,hrd,hrθ,hrs⟩ := exists_balanced_annular_approximation N (by omega) ξ
  have hRp : 0 < R := by linarith
  have hlower := outsideSourceMajorArcs_effective_lower (by omega : 1 ≤ N) hRp hout r
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log ((N : ℝ)/2) := Real.log_nonneg (by linarith)
  by_cases hd : (r.den : ℝ) ≤ ((N : ℝ)/2)^(1/2 : ℝ)
  · have hm := annularMangoldt_Ren_scale_bound hN r.den r.den_pos ξ (ξ-(r : ℝ)) c
      hC hR hpow hd hrθ hlower (hRen r hd hrθ)
    exact hm.trans (le_add_of_nonneg_right
      (mul_nonneg (ghoshSourceConstant_nonneg hB) (Real.rpow_nonneg hRp.le _)))
  · have hdl : ((N : ℝ)/2)^(1/2 : ℝ) ≤ (r.den : ℝ) := le_of_not_ge hd
    have hm := annularMangoldt_Ghosh_scale_bound (by omega : 1 ≤ N) ξ hB hRp hpow
      hdl hrd (hGhosh r hdl hrd hrs)
    exact hm.trans (le_add_of_nonneg_left (by
      exact mul_nonneg (mul_nonneg (renSourceConstant_nonneg hC) (Real.rpow_nonneg hl _))
        (Real.rpow_nonneg hRp.le _)))

end PrimeSquares
