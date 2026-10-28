import PrimeSquares.BinaryNodeCoordinateSummability
open scoped lp
namespace PrimeSquares
theorem binaryNode_spatial_total (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    (∑' x : ℤ,binaryNodeSquareEnergy h a (fun k b => G k b x))=binaryNodeNormEnergy h a G := by
  induction h generalizing a with
  | zero => exact real_l2_square_total (G 0 a)
  | succ h ih =>
    have hs := real_l2_square_summable (G (h+1) a)
    change (∑' x : ℤ,((G (h+1) a x)^2+binaryNodeSquareEnergy h a (fun k b => G k b x)+
      binaryNodeSquareEnergy h (a+2^h) (fun k b => G k b x)))=_
    rw [Summable.tsum_add (hs.add (binaryNode_coordinate_summable h a G)) (binaryNode_coordinate_summable h (a+2^h) G),
      Summable.tsum_add hs (binaryNode_coordinate_summable h a G),real_l2_square_total,ih a,ih (a+2^h)]
    rfl
end PrimeSquares
