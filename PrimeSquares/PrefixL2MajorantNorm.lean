import PrimeSquares.PrefixL2Majorant
open scoped lp
namespace PrimeSquares
theorem prefixL2Majorant_norm (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    ‖prefixL2Majorant h a F‖=Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryTreeL2Energy h a F) := by
  rw [prefixL2Majorant,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),binaryTreeEnvelope_norm]
end PrimeSquares
