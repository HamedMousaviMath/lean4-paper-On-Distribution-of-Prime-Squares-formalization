import PrimeSquares.GeometricEnergyPotential
namespace PrimeSquares
theorem geometricEnergyPotential_difference (x : ℝ) :
    geometricEnergyPotential x-geometricEnergyPotential (4*x)=
      15*x^2/((1+x^2)*(1+16*x^2)) := by
  unfold geometricEnergyPotential
  have h1 : 1+x^2 ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1+(4*x)^2 ≠ 0 := ne_of_gt (by positivity)
  have h3 : 1+16*x^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring
end PrimeSquares
