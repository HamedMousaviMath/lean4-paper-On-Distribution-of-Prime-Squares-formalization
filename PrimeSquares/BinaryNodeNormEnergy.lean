import PrimeSquares.BinaryNodeSquareEnergy
open scoped lp
namespace PrimeSquares
noncomputable def binaryNodeNormEnergy : ℕ → ℕ → (ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) → ℝ
  | 0,a,G => ‖G 0 a‖^2
  | h+1,a,G => ‖G (h+1) a‖^2+binaryNodeNormEnergy h a G+binaryNodeNormEnergy h (a+2^h) G
theorem binaryNodeNormEnergy_nonneg (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) :
    0 ≤ binaryNodeNormEnergy h a G := by
  induction h generalizing a with
  | zero => exact sq_nonneg _
  | succ h ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih a)) (ih _)
end PrimeSquares
