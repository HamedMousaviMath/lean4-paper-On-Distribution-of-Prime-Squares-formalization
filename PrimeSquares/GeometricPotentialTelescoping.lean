import PrimeSquares.GeometricPotentialDifference
import Mathlib.Algebra.BigOperators.Intervals
open Finset
namespace PrimeSquares
theorem geometricEnergyPotential_telescoping (x : ℝ) (n : ℕ) :
    (∑ j ∈ range n,(geometricEnergyPotential ((4 : ℝ)^j*x)-
      geometricEnergyPotential ((4 : ℝ)^(j+1)*x)))=
      geometricEnergyPotential x-geometricEnergyPotential ((4 : ℝ)^n*x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih];ring
end PrimeSquares
