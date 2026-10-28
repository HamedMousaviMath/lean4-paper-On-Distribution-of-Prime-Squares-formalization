import PrimeSquares.RealL2SquareEnergy
namespace PrimeSquares
noncomputable def binaryNodeSquareEnergy : ℕ → ℕ → (ℕ → ℕ → ℝ) → ℝ
  | 0,a,v => (v 0 a)^2
  | h+1,a,v => (v (h+1) a)^2+binaryNodeSquareEnergy h a v+binaryNodeSquareEnergy h (a+2^h) v
theorem binaryNodeSquareEnergy_nonneg (h a : ℕ) (v : ℕ → ℕ → ℝ) : 0 ≤ binaryNodeSquareEnergy h a v := by
  induction h generalizing a with
  | zero => exact sq_nonneg _
  | succ h ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih a)) (ih _)
end PrimeSquares
