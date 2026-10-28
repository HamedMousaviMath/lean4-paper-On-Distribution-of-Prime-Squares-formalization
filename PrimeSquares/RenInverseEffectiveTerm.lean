import PrimeSquares.RenSmallDenominatorTerms

namespace PrimeSquares

theorem weighted_inverse_sqrt_effective {q T R : ℝ} (hq : 0 ≤ q)
    (hR : 0 < R) (hqT : q ≤ T) (hTR : R/4 ≤ T) :
    q^(1/12 : ℝ)/Real.sqrt T ≤
      (4 : ℝ)^(5/12 : ℝ)*R^(-(5/12 : ℝ)) := by
  have hTp : 0 < T := (by positivity : 0 < R/4).trans_le hTR
  calc
    _ ≤ T^(1/12 : ℝ)/Real.sqrt T := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hq hqT (by norm_num)) (Real.sqrt_nonneg T)
    _ = T^(-(5/12 : ℝ)) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_sub hTp]
      norm_num
    _ ≤ (R/4)^(-(5/12 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hTR (by norm_num)
    _ = _ := by
      rw [Real.div_rpow hR.le (by norm_num : (0 : ℝ) ≤ 4),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),div_inv_eq_mul,mul_comm]

theorem ren_third_weighted_term {x q T R : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hR : 0 < R) (hqT : q ≤ T) (hTR : R/4 ≤ T) :
    q^(1/12 : ℝ)*(x/Real.sqrt T)/x ≤
      (4 : ℝ)^(5/12 : ℝ)*R^(-(5/12 : ℝ)) := by
  have he : q^(1/12 : ℝ)*(x/Real.sqrt T)/x = q^(1/12 : ℝ)/Real.sqrt T := by
    field_simp [hx.ne']
  rw [he]
  exact weighted_inverse_sqrt_effective hq hR hqT hTR

end PrimeSquares
