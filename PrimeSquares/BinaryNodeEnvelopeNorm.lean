import PrimeSquares.BinaryNodeL2Envelope
open scoped lp
namespace PrimeSquares
theorem binaryNodeEnvelope_norm_square (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    ‖binaryNodeEnvelope h a G‖^2=binaryNodeNormEnergy h a G := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (binaryNodeEnvelope h a G)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,binaryNodeEnvelope,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (binaryNodeSquareEnergy_nonneg h a _),binaryNode_spatial_total] using hh
theorem binaryNodeEnvelope_norm (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    ‖binaryNodeEnvelope h a G‖=Real.sqrt (binaryNodeNormEnergy h a G) := by
  rw [←binaryNodeEnvelope_norm_square h a G,Real.sqrt_sq (norm_nonneg _)]
end PrimeSquares
