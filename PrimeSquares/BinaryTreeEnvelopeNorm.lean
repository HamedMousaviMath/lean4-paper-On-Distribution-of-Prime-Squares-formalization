import PrimeSquares.BinaryTreeL2Envelope
open scoped lp
namespace PrimeSquares
theorem binaryTreeEnvelope_norm_square (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    ‖binaryTreeEnvelope h a F‖^2=binaryTreeL2Energy h a F := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (binaryTreeEnvelope h a F)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,binaryTreeEnvelope,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (binaryTreeSquareEnergy_nonneg h a _),binaryTree_spatial_total] using hh
theorem binaryTreeEnvelope_norm (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    ‖binaryTreeEnvelope h a F‖=Real.sqrt (binaryTreeL2Energy h a F) := by
  rw [←binaryTreeEnvelope_norm_square h a F,Real.sqrt_sq (norm_nonneg _)]
end PrimeSquares
