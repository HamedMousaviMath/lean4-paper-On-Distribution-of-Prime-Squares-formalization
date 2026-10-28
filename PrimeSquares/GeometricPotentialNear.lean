import PrimeSquares.GeometricPotentialDifference
namespace PrimeSquares
theorem geometricEnergyPotential_near {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x^2 ≤ (34/15 : ℝ)*(geometricEnergyPotential x-geometricEnergyPotential (4*x)) := by
  have hy : x^2 ≤ 1 := by nlinarith
  have hy2 : (x^2)^2 ≤ x^2 := by nlinarith [mul_le_mul_of_nonneg_right hy (sq_nonneg x)]
  have hd : (1+x^2)*(1+16*x^2) ≤ 34 := by nlinarith [sq_nonneg x]
  rw [geometricEnergyPotential_difference]
  calc
    x^2 ≤ 34*x^2/((1+x^2)*(1+16*x^2)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg x)]
    _ = _ := by ring
end PrimeSquares
