import PrimeSquares.OrdinaryLowWidth
import PrimeSquares.ExceptionalLowWidth

namespace PrimeSquares

theorem ordinaryLowWidth_two_le {N Q q : ℝ} (hQ : 0 < Q) (hq : 1 ≤ q)
    (hb : 2*Q ≤ N^2) : 2 ≤ ordinaryLowWidth N Q q := by
  unfold ordinaryLowWidth
  apply (le_div_iff₀ hQ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg N)]

theorem exceptionalLowWidth_two_le {N Q B d : ℝ} (hQ : 0 < Q) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hb : 2*Q ≤ N^2) : 2 ≤ exceptionalLowWidth N Q B d := by
  have hBd : 1 ≤ B*d := one_le_mul_of_one_le_of_one_le hB hd
  unfold exceptionalLowWidth
  apply (le_div_iff₀ hQ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hBd (sq_nonneg N)]

end PrimeSquares
