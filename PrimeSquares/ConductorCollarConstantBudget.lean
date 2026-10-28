import PrimeSquares.ConductorCollarEnvelopeEnergy
namespace PrimeSquares
theorem conductorCollar_constant_budget {Q C T η ε : ℝ} (hQ : 0 < Q) (hC : 0 < C)
    (hη0 : 0 ≤ η) (hη1 : η < 1) {q₀ : ℕ} (hq₀ : 0 < q₀)
    (hT : conductorMajorant q₀/(q₀ : ℝ) ≤ T) :
    collarPowerConstant C η*(q₀ : ℝ)^(-ε)*(effectiveCollarCutoff Q q₀)^(-η) ≤
      (collarPowerConstant C η*T^η)*Q^(-η)*(q₀ : ℝ)^(-ε) := by
  have hp : 0 < collarPowerConstant C η := collarPowerConstant_pos hC hη1
  calc
    _ ≤ collarPowerConstant C η*(q₀ : ℝ)^(-ε)*(Q^(-η)*T^η) :=
      mul_le_mul_of_nonneg_left (effectiveCollarCutoff_power_bound hQ hη0 hq₀ hT) (by positivity)
    _ = _ := by ring
end PrimeSquares
