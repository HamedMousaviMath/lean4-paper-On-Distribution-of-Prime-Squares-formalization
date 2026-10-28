import PrimeSquares.QuadraticResidueIndicator

set_option autoImplicit false
namespace PrimeSquares

theorem bounded_power_difference {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (k : ℕ) :
    |x^k-y^k| ≤ (k : ℝ)*|x-y| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hyk : 0 ≤ y^k := pow_nonneg hy0 k
    have hyk1 : y^k ≤ 1 := pow_le_one₀ hy0 hy1
    have h1 := mul_le_mul ih hx1 hx0 (by positivity : 0 ≤ (k : ℝ)*|x-y|)
    have h2 := mul_le_mul_of_nonneg_right hyk1 (abs_nonneg (x-y))
    calc
      |x^(k+1)-y^(k+1)| = |(x^k-y^k)*x+y^k*(x-y)| := by congr 1; ring
      _ ≤ |(x^k-y^k)*x|+|y^k*(x-y)| := abs_add_le _ _
      _ = |x^k-y^k| *x+y^k*|x-y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hyk]
      _ ≤ (k : ℝ)*|x-y|+|x-y| := by linarith
      _ = ((k+1 : ℕ) : ℝ)*|x-y| := by push_cast; ring

end PrimeSquares
