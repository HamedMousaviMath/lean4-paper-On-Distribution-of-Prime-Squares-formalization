import PrimeSquares.DyadicAnnularScales

namespace PrimeSquares

theorem dyadic_narrow_width (M j : ℕ) (q Q : ℝ) :
    q*((((2 : ℕ)^j*M : ℕ) : ℝ)^2)/Q=(4 : ℝ)^j*(q*(M : ℝ)^2/Q) := by
  rw [dyadic_square_scale]
  ring

theorem dyadic_narrow_width_pos {M : ℕ} (hM : 0 < M) (j : ℕ) {q Q : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) : 0 < q*((((2 : ℕ)^j*M : ℕ) : ℝ)^2)/Q := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  rw [dyadic_narrow_width]
  positivity

end PrimeSquares
