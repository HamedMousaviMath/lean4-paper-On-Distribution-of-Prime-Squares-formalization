import PrimeSquares.GeometricPotentialDifference
namespace PrimeSquares
theorem geometricEnergyPotential_far {x : ℝ} (hx : 1 ≤ x) :
    1/x^2 ≤ (34/15 : ℝ)*(geometricEnergyPotential x-geometricEnergyPotential (4*x)) := by
  have hy : 1 ≤ x^2 := by nlinarith
  have hy2 : x^2 ≤ (x^2)^2 := by nlinarith [mul_le_mul_of_nonneg_right hy (sq_nonneg x)]
  have hd : (1+x^2)*(1+16*x^2) ≤ 34*(x^2)^2 := by nlinarith
  have hp : 0 < x^2 := by positivity
  rw [geometricEnergyPotential_difference]
  calc
    1/x^2 ≤ 34*x^2/((1+x^2)*(1+16*x^2)) := by
      apply (div_le_div_iff₀ hp (by positivity)).mpr
      nlinarith only [hd]
    _ = _ := by ring
end PrimeSquares
