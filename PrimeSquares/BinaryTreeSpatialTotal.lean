import PrimeSquares.BinaryTreeCoordinateSummability
open scoped lp
namespace PrimeSquares
theorem binaryTree_spatial_total (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    (∑' x : ℤ,binaryTreeSquareEnergy h a (fun i => F i x))=binaryTreeL2Energy h a F := by
  induction h generalizing a with
  | zero => exact l2_square_tsum (F a)
  | succ h ih =>
    have hs := (l2_square_hasSum (intervalL2Sum a (2^(h+1)) F)).summable
    simp only [binaryTreeSquareEnergy,←intervalL2Sum_apply]
    rw [Summable.tsum_add (hs.add (binaryTree_coordinate_summable h a F)) (binaryTree_coordinate_summable h (a+2^h) F),
      Summable.tsum_add hs (binaryTree_coordinate_summable h a F),l2_square_tsum,ih a,ih (a+2^h)]
    rfl
end PrimeSquares
