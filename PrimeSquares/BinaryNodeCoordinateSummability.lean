import PrimeSquares.BinaryNodeNormEnergy
open scoped lp
namespace PrimeSquares
theorem binaryNode_coordinate_summable (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    Summable (fun x : ℤ => binaryNodeSquareEnergy h a (fun k b => G k b x)) := by
  induction h generalizing a with
  | zero => exact real_l2_square_summable (G 0 a)
  | succ h ih => exact ((real_l2_square_summable (G (h+1) a)).add (ih a)).add (ih (a+2^h))
end PrimeSquares
