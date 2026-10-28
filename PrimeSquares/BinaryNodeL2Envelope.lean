import PrimeSquares.BinaryNodeSpatialTotal
open scoped lp
namespace PrimeSquares
noncomputable def binaryNodeEnvelope (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun x => Real.sqrt (binaryNodeSquareEnergy h a (fun k b => G k b x)),by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt (binaryNodeSquareEnergy_nonneg h a _)] using binaryNode_coordinate_summable h a G⟩
theorem binaryNodeEnvelope_nonneg (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (x : ℤ) :
    0 ≤ binaryNodeEnvelope h a G x := Real.sqrt_nonneg _
end PrimeSquares
