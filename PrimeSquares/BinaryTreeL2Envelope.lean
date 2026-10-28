import PrimeSquares.BinaryTreeSpatialTotal
open scoped lp
namespace PrimeSquares
noncomputable def binaryTreeEnvelope (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun x => Real.sqrt (binaryTreeSquareEnergy h a (fun i => F i x)),by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt (binaryTreeSquareEnergy_nonneg h a _)] using binaryTree_coordinate_summable h a F⟩
theorem binaryTreeEnvelope_nonneg (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (x : ℤ) : 0 ≤ binaryTreeEnvelope h a F x := Real.sqrt_nonneg _
end PrimeSquares
