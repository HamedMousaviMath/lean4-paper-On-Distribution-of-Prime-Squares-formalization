import PrimeSquares.BinaryTreeL2Energy
open scoped lp
namespace PrimeSquares
theorem binaryTree_coordinate_summable (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) :
    Summable (fun x : ℤ => binaryTreeSquareEnergy h a (fun i => F i x)) := by
  induction h generalizing a with
  | zero => exact (l2_square_hasSum (F a)).summable
  | succ h ih =>
    have hs := ((l2_square_hasSum (intervalL2Sum a (2^(h+1)) F)).summable.add (ih a)).add (ih (a+2^h))
    simpa only [binaryTreeSquareEnergy,intervalL2Sum_apply] using hs
end PrimeSquares
