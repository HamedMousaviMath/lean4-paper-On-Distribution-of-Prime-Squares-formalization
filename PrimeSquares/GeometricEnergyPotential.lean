import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
namespace PrimeSquares
noncomputable def geometricEnergyPotential (x : ℝ) : ℝ := 1/(1+x^2)
theorem geometricEnergyPotential_range (x : ℝ) :
    0 ≤ geometricEnergyPotential x ∧ geometricEnergyPotential x ≤ 1 := by
  unfold geometricEnergyPotential
  exact ⟨by positivity,(div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg x])⟩
end PrimeSquares
