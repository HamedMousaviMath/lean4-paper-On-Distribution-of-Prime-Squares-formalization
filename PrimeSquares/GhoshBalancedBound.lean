import PrimeSquares.RenMinorArcBound
import PrimeSquares.IntermediateCircleApproximation

namespace PrimeSquares

noncomputable def ghoshQuadraticBracket (x q : ℝ) : ℝ :=
  1/q + x^(-(1/2 : ℝ)) + q/x^2

theorem ghoshQuadraticBracket_nonneg {x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    0 ≤ ghoshQuadraticBracket x q := by
  dsimp [ghoshQuadraticBracket]
  positivity

theorem ghoshQuadraticBracket_balanced {x q : ℝ} (hx : 0 < x)
    (hql : x^(1/2 : ℝ) ≤ q) (hqu : q ≤ x^(3/2 : ℝ)) :
    ghoshQuadraticBracket x q ≤ 3*x^(-(1/2 : ℝ)) := by
  have hp := Real.rpow_pos_of_pos hx (1/2 : ℝ)
  have hq : 0 < q := hp.trans_le hql
  have hl : 1/q ≤ x^(-(1/2 : ℝ)) := by
    rw [Real.rpow_neg hx.le]
    simpa only [one_div] using one_div_le_one_div_of_le hp hql
  have hu : q/x^2 ≤ x^(-(1/2 : ℝ)) := by
    calc
      _ ≤ x^(3/2 : ℝ)/x^2 := div_le_div_of_nonneg_right hqu (sq_nonneg x)
      _ = x^((3/2 : ℝ)-2) := by rw [Real.rpow_sub hx];norm_num
      _ = _ := by norm_num
  dsimp [ghoshQuadraticBracket]
  linarith

theorem ghoshBalanced_fourth_root {x q : ℝ} (hx : 0 < x)
    (hql : x^(1/2 : ℝ) ≤ q) (hqu : q ≤ x^(3/2 : ℝ)) :
    (ghoshQuadraticBracket x q)^(1/4 : ℝ) ≤
      (3 : ℝ)^(1/4 : ℝ)*x^(-(1/8 : ℝ)) := by
  have hb := ghoshQuadraticBracket_balanced hx hql hqu
  have hq : 0 < q := (Real.rpow_pos_of_pos hx (1/2 : ℝ)).trans_le hql
  calc
    _ ≤ (3*x^(-(1/2 : ℝ)))^(1/4 : ℝ) :=
      Real.rpow_le_rpow (ghoshQuadraticBracket_nonneg hx hq) hb (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Real.rpow_nonneg hx.le _),
        ←Real.rpow_mul hx.le]
      norm_num

theorem annularMangoldt_from_Ghosh_bound (N : ℕ) (ξ B q ε : ℝ)
    (hGhosh : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      B*((N : ℝ)/2)^(1+ε)*(ghoshQuadraticBracket ((N : ℝ)/2) q)^(1/4 : ℝ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      B*((N : ℝ)/2)^(1+ε)*(ghoshQuadraticBracket ((N : ℝ)/2) q)^(1/4 : ℝ)/N := by
  rw [annularMangoldtSymbol_norm_Ren]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hGhosh (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem annularMangoldt_Ghosh_balanced {N : ℕ} (hN : 1 ≤ N)
    (ξ : ℝ) {B q : ℝ} (hB : 0 ≤ B)
    (hql : ((N : ℝ)/2)^(1/2 : ℝ) ≤ q)
    (hqu : q ≤ ((N : ℝ)/2)^(3/2 : ℝ))
    (hGhosh : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      B*((N : ℝ)/2)^(17/16 : ℝ)*
        (ghoshQuadraticBracket ((N : ℝ)/2) q)^(1/4 : ℝ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      (B*(3 : ℝ)^(1/4 : ℝ)/2)*((N : ℝ)/2)^(-(1/16 : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ)/2 := by positivity
  have hb := ghoshBalanced_fourth_root hx hql hqu
  have hs := annularMangoldt_from_Ghosh_bound N ξ B q (1/16) (by norm_num;exact hGhosh)
  norm_num at hs
  calc
    _ ≤ B*((N : ℝ)/2)^(17/16 : ℝ)*
        (ghoshQuadraticBracket ((N : ℝ)/2) q)^(1/4 : ℝ)/N := hs
    _ ≤ B*((N : ℝ)/2)^(17/16 : ℝ)*
        ((3 : ℝ)^(1/4 : ℝ)*((N : ℝ)/2)^(-(1/8 : ℝ)))/N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hn.le
    _ = _ := by
      have hp : ((N : ℝ)/2)^(17/16 : ℝ)*((N : ℝ)/2)^(-(1/8 : ℝ)) =
          ((N : ℝ)/2)*((N : ℝ)/2)^(-(1/16 : ℝ)) := by
        rw [←Real.rpow_add hx,show (17/16 : ℝ)+-(1/8 : ℝ) = 1+-(1/16 : ℝ) by norm_num,
          Real.rpow_add hx,Real.rpow_one]
      calc
        _ = (B*(3 : ℝ)^(1/4 : ℝ)/N)*
            (((N : ℝ)/2)^(17/16 : ℝ)*((N : ℝ)/2)^(-(1/8 : ℝ))) := by ring
        _ = _ := by rw [hp];field_simp [hn.ne']

end PrimeSquares
