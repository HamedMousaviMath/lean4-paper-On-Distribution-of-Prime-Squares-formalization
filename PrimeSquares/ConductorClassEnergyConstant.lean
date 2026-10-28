import PrimeSquares.FiniteConductorClassBudget
namespace PrimeSquares
noncomputable def conductorClassEnergyConstant (ε : ℝ) : ℝ := Real.sqrt ((1-(2 : ℝ)^(-(2*ε)))⁻¹)
theorem conductorClassEnergyConstant_pos {ε : ℝ} (hε : 0 < ε) : 0 < conductorClassEnergyConstant ε := by
  unfold conductorClassEnergyConstant
  exact Real.sqrt_pos.mpr (inv_pos.mpr (geometric_inverse_power_denominator_pos (by linarith : 0 < 2*ε)))
theorem conductorClassEnergyConstant_sq {ε : ℝ} (hε : 0 < ε) :
    (conductorClassEnergyConstant ε)^2=(1-(2 : ℝ)^(-(2*ε)))⁻¹ := by
  apply Real.sq_sqrt
  exact (inv_pos.mpr (geometric_inverse_power_denominator_pos (by linarith : 0 < 2*ε))).le
end PrimeSquares
