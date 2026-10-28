import PrimeSquares.GeometricPotentialNear
import PrimeSquares.GeometricPotentialFar
namespace PrimeSquares
theorem twoSidedError_potential {C x e : ℝ} (_hC : 0 ≤ C) (hx : 0 ≤ x) (he : 0 ≤ e)
    (hn : e ≤ C*x) (hf : x*e ≤ C) :
    e^2 ≤ (34/15 : ℝ)*C^2*(geometricEnergyPotential x-geometricEnergyPotential (4*x)) := by
  by_cases h : x ≤ 1
  · calc
      e^2 ≤ (C*x)^2 := pow_le_pow_left₀ he hn 2
      _ = C^2*x^2 := by ring
      _ ≤ C^2*((34/15 : ℝ)*(geometricEnergyPotential x-geometricEnergyPotential (4*x))) :=
        mul_le_mul_of_nonneg_left (geometricEnergyPotential_near hx h) (sq_nonneg _)
      _ = _ := by ring
  · have hp : 0 < x := by linarith
    have hd : e ≤ C/x := (le_div_iff₀ hp).mpr (by nlinarith only [hf])
    calc
      e^2 ≤ (C/x)^2 := pow_le_pow_left₀ he hd 2
      _ = C^2*(1/x^2) := by ring
      _ ≤ C^2*((34/15 : ℝ)*(geometricEnergyPotential x-geometricEnergyPotential (4*x))) :=
        mul_le_mul_of_nonneg_left (geometricEnergyPotential_far (by linarith)) (sq_nonneg _)
      _ = _ := by ring
end PrimeSquares
