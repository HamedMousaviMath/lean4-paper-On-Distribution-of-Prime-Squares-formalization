import PrimeSquares.FiniteBinaryCapacity
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem finiteBinaryDepth_le_log2 (L : ℕ) : finiteBinaryDepth L ≤ Nat.log2 L+1 := by
  apply Nat.clog_le_of_le_pow
  simpa only [Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
    (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1<2) L))
theorem finiteBinaryDepth_factor_le (L : ℕ) :
    (finiteBinaryDepth L+1 : ℝ) ≤ (Nat.log2 L+2 : ℝ) := by
  exact_mod_cast (by have h := finiteBinaryDepth_le_log2 L;omega : finiteBinaryDepth L+1 ≤ Nat.log2 L+2)
end PrimeSquares
