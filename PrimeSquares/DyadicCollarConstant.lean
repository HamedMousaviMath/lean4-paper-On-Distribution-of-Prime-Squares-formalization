import PrimeSquares.DyadicCoefficientBudget

namespace PrimeSquares

theorem dyadic_collar_constant_identity (C Q δ : ℝ) (s : ℕ) :
    96*(C*((2 : ℝ)^s)^(-δ))*(2 : ℝ)^(s+1)/(Real.pi*Q)=
      (192*C/(Real.pi*Q))*((2 : ℝ)^(1-δ))^s := by
  have hp : 0 < (2 : ℝ)^s := by positivity
  have he : ((2 : ℝ)^s)^(-δ)*(2 : ℝ)^s=((2 : ℝ)^(1-δ))^s := by
    calc
      _ = ((2 : ℝ)^s)^(-δ+1) := by rw [Real.rpow_add hp,Real.rpow_one]
      _ = (2 : ℝ)^((s : ℝ)*(-δ+1)) := (Real.rpow_natCast_mul (by norm_num) s (-δ+1)).symm
      _ = (2 : ℝ)^((1-δ)*(s : ℝ)) := by congr 1;ring
      _ = _ := Real.rpow_mul_natCast (by norm_num) (1-δ) s
  calc
    _ = (192*C/(Real.pi*Q))*(((2 : ℝ)^s)^(-δ)*(2 : ℝ)^s) := by rw [pow_succ];ring
    _ = _ := by rw [he]

end PrimeSquares
