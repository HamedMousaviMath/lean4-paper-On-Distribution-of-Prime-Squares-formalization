import PrimeSquares.RealCutoffDisjointMaximum
import Mathlib.Data.Nat.Log
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
def finiteBinaryDepth (L : ℕ) : ℕ := Nat.clog 2 L
theorem finiteBinaryDepth_capacity (L : ℕ) : L ≤ 2^finiteBinaryDepth L :=
  Nat.le_pow_clog (by norm_num) L
theorem finiteBinaryDepth_zero : finiteBinaryDepth 0=0 := by simp [finiteBinaryDepth]
end PrimeSquares
