import PrimeSquares.TwoSidedErrorPotential
import PrimeSquares.GeometricPotentialTelescoping
open Finset
namespace PrimeSquares
theorem geometricError_range_energy {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (e : ℕ → ℝ)
    (he : ∀ j,0 ≤ e j) (hn : ∀ j,e j ≤ C*((4 : ℝ)^j*x))
    (hf : ∀ j,((4 : ℝ)^j*x)*e j ≤ C) (n : ℕ) :
    (∑ j ∈ range n,(e j)^2) ≤ (34/15 : ℝ)*C^2 := by
  calc
    _ ≤ ∑ j ∈ range n,(34/15 : ℝ)*C^2*
        (geometricEnergyPotential ((4 : ℝ)^j*x)-geometricEnergyPotential ((4 : ℝ)^(j+1)*x)) := by
      apply sum_le_sum
      intro j _
      have h := twoSidedError_potential hC (by positivity : 0 ≤ (4 : ℝ)^j*x) (he j) (hn j) (hf j)
      have heq : (4 : ℝ)^(j+1)*x=4*((4 : ℝ)^j*x) := by rw [pow_succ];ring
      simpa only [heq] using h
    _ = (34/15 : ℝ)*C^2*(geometricEnergyPotential x-geometricEnergyPotential ((4 : ℝ)^n*x)) := by
      rw [←mul_sum,geometricEnergyPotential_telescoping]
    _ ≤ (34/15 : ℝ)*C^2*1 := mul_le_mul_of_nonneg_left
      (by linarith [(geometricEnergyPotential_range x).2,
        (geometricEnergyPotential_range ((4 : ℝ)^n*x)).1]) (by positivity)
    _ = _ := mul_one _
end PrimeSquares
