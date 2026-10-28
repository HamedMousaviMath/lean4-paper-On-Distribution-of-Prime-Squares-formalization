import PrimeSquares.BinaryTreeEnvelopeNorm
open scoped lp
namespace PrimeSquares
noncomputable def prefixL2Majorant (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  Real.sqrt (h+1 : ℝ) • binaryTreeEnvelope h a F
theorem prefixL2Majorant_dominates (h a K : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (hK : K ≤ 2^h) (x : ℤ) :
    ‖intervalL2Sum a K F x‖ ≤ prefixL2Majorant h a F x := by
  rw [intervalL2Sum_apply]
  exact binary_prefix_norm_envelope h a K (fun i => F i x) hK
theorem prefixL2Majorant_nonneg (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (x : ℤ) : 0 ≤ prefixL2Majorant h a F x := by
  exact mul_nonneg (Real.sqrt_nonneg _) (binaryTreeEnvelope_nonneg h a F x)
end PrimeSquares
