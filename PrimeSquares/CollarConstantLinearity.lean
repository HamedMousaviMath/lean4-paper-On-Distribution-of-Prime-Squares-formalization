import PrimeSquares.ConductorGaussEnvelope
namespace PrimeSquares
theorem collarPowerConstant_mul (C a δ : ℝ) : collarPowerConstant (C*a) δ=collarPowerConstant C δ*a := by
  unfold collarPowerConstant
  ring
end PrimeSquares
