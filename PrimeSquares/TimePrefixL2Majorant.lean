import PrimeSquares.TimePrefixPointwiseEnvelope
open scoped lp
namespace PrimeSquares
noncomputable def timePrefixL2Majorant (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) : lp (fun _ : ℤ => ℝ) 2 :=
  Real.sqrt (h+1 : ℝ) • binaryNodeEnvelope h a G
theorem timePrefixL2Majorant_nonneg (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (x : ℤ) :
    0 ≤ timePrefixL2Majorant h a G x := mul_nonneg (Real.sqrt_nonneg _) (binaryNodeEnvelope_nonneg h a G x)
theorem timePrefixL2Majorant_norm (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    ‖timePrefixL2Majorant h a G‖=Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryNodeNormEnergy h a G) := by
  rw [timePrefixL2Majorant,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),binaryNodeEnvelope_norm]
end PrimeSquares
