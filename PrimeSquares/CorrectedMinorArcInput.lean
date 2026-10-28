import PrimeSquares.ComplementaryMinorArcBound

set_option autoImplicit false
namespace PrimeSquares

/-- The actual Ren bound retains all three terms and its effective denominator. -/
theorem annularMangoldt_complete_Ren_bound (N : ℕ) (ξ B T : ℝ)
    (hRen : ‖renQuadraticSum ((N:ℝ)/2) ξ‖≤B*renQuadraticBracket ((N:ℝ)/2) T) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ:PrimeCircle)‖≤
      B*((Real.sqrt ((N:ℝ)/2)*Real.sqrt T)/N + ((N:ℝ)/2)^(4/5:ℝ)/N +
        (((N:ℝ)/2)/Real.sqrt T)/N) := by
  exact (annularMangoldt_from_Ren_bound N ξ B T hRen).trans_eq (by unfold renQuadraticBracket; ring)

theorem complementaryMinorBudget_quarter_bound {N : ℕ} (hN : 2≤N)
    {C B d R : ℝ} (hC : 0≤C) (hB : 0≤B) (hd : 0≤d) (hR : 1≤R)
    (hlog : 1≤Real.log N) :
    complementaryMinorBudget N C B d R≤
      (renSourceConstant C+ghoshSourceConstant B)*(Real.log N)^d*R^(-(1/4:ℝ)) := by
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hl0 : 0≤Real.log ((N:ℝ)/2) := Real.log_nonneg (by linarith)
  have hl : Real.log ((N:ℝ)/2)≤Real.log N := Real.log_le_log (by positivity) (by linarith)
  have hp : (Real.log ((N:ℝ)/2))^d≤(Real.log N)^d := Real.rpow_le_rpow hl0 hl hd
  have hp1 : 1≤(Real.log N)^d := Real.one_le_rpow hlog hd
  have hquarter : R^(-(5/12:ℝ))≤R^(-(1/4:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hren0 := renSourceConstant_nonneg hC
  have hghosh0 := ghoshSourceConstant_nonneg hB
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp hren0) hquarter
    (Real.rpow_nonneg (by linarith) _) (mul_nonneg hren0 (Real.rpow_nonneg (by linarith) _))
  have hh' := mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right hghosh0 hp1) (Real.rpow_nonneg (by linarith : 0≤R) (-(1/4:ℝ)))
  unfold complementaryMinorBudget
  nlinarith only [hh,hh']

/-- A sufficient full complementary estimate for the approximation argument. -/
theorem annularMangoldt_outside_major_quarter_bound {N : ℕ} (hN : 4≤N)
    {C B d R ξ : ℝ} (hC : 0≤C) (hB : 0≤B) (hd : 0≤d) (hR : 1≤R)
    (hpow : R^4≤(N:ℝ)/2) (hlog : 1≤Real.log N)
    (hout : OutsideSourceMajorArcs N R ξ)
    (hRen : RenBalancedInput N ξ C d) (hGhosh : GhoshBalancedInput N ξ B) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ:PrimeCircle)‖≤
      (renSourceConstant C+ghoshSourceConstant B)*(Real.log N)^d*R^(-(1/4:ℝ)) :=
  (annularMangoldt_complementary_minor_bound hN hC hB hR hpow hout hRen hGhosh).trans
    (complementaryMinorBudget_quarter_bound (by omega) hC hB hd hR hlog)

end PrimeSquares
