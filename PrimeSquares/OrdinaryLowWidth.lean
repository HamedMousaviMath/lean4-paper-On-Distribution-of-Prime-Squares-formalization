import PrimeSquares.SmoothedAnnularDecay

namespace PrimeSquares

noncomputable def ordinaryLowWidth (N Q q : ℝ) : ℝ := q*N^2/Q

theorem ordinaryLowWidth_pos {N Q q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hq : 0 < q) :
    0 < ordinaryLowWidth N Q q := by unfold ordinaryLowWidth;positivity

theorem ordinaryLowWidth_le_square {N Q q : ℝ} (_hN : 0 ≤ N) (hQ : 0 < Q) (hqQ : q ≤ Q) :
    ordinaryLowWidth N Q q ≤ N^2 := by
  unfold ordinaryLowWidth
  apply (div_le_iff₀ hQ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hqQ (sq_nonneg N)]

theorem ordinaryLowWidth_reciprocal {N Q q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hq : 0 < q) :
    (ordinaryLowWidth N Q q)⁻¹=Q/(q*N^2) := by
  unfold ordinaryLowWidth
  field_simp

end PrimeSquares
