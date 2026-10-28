import PrimeSquares.BalancedEffectiveDenominator
import PrimeSquares.RenDivisorBudget

namespace PrimeSquares

theorem rpow_product_div_self {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x^a*x^b/x = x^(a+b-1) := by
  rw [←Real.rpow_add hx]
  calc
    _ = x^(a+b)/x^(1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := (Real.rpow_sub hx _ _).symm

theorem smallDenominator_twelfth {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hql : q ≤ x^(1/2 : ℝ)) : q^(1/12 : ℝ) ≤ x^(1/24 : ℝ) := by
  have h := Real.rpow_le_rpow hq hql (by norm_num : (0 : ℝ) ≤ 1/12)
  rw [←Real.rpow_mul hx.le] at h
  norm_num at h
  exact h

theorem effectiveDenominator_sqrt_bound {x T : ℝ} (hx : 0 < x)
    (hT : T ≤ 2*x^(1/2 : ℝ)) :
    Real.sqrt T ≤ Real.sqrt 2*x^(1/4 : ℝ) := by
  calc
    _ ≤ Real.sqrt (2*x^(1/2 : ℝ)) := Real.sqrt_le_sqrt hT
    _ = _ := by
      simp only [Real.sqrt_eq_rpow]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hx.le _),
        ←Real.rpow_mul hx.le]
      norm_num

theorem ren_first_weighted_term {x q T : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hql : q ≤ x^(1/2 : ℝ)) (hT : T ≤ 2*x^(1/2 : ℝ)) :
    q^(1/12 : ℝ)*(Real.sqrt x*Real.sqrt T)/x ≤
      Real.sqrt 2*x^(-(5/24 : ℝ)) := by
  have hqpow := smallDenominator_twelfth hx hq hql
  have hs := effectiveDenominator_sqrt_bound hx hT
  have he : x^(1/24 : ℝ)*(Real.sqrt x*x^(1/4 : ℝ))/x = x^(-(5/24 : ℝ)) := by
    rw [Real.sqrt_eq_rpow,←mul_assoc,←Real.rpow_add hx,rpow_product_div_self hx]
    norm_num
  calc
    _ ≤ x^(1/24 : ℝ)*(Real.sqrt x*(Real.sqrt 2*x^(1/4 : ℝ)))/x := by gcongr
    _ = Real.sqrt 2*(x^(1/24 : ℝ)*(Real.sqrt x*x^(1/4 : ℝ))/x) := by ring
    _ = _ := by rw [he]

theorem ren_middle_weighted_term {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hql : q ≤ x^(1/2 : ℝ)) :
    q^(1/12 : ℝ)*x^(4/5 : ℝ)/x ≤ x^(-(19/120 : ℝ)) := by
  calc
    _ ≤ x^(1/24 : ℝ)*x^(4/5 : ℝ)/x := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (smallDenominator_twelfth hx hq hql)
          (Real.rpow_nonneg hx.le _)) hx.le
    _ = _ := by rw [rpow_product_div_self hx];norm_num

end PrimeSquares
