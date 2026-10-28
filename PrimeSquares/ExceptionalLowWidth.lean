import PrimeSquares.OrdinaryLowWidth
import PrimeSquares.ConductorFactors

namespace PrimeSquares

noncomputable def exceptionalLowWidth (N Q B d : ℝ) : ℝ := B*d*N^2/Q

theorem exceptionalLowWidth_pos {N Q B d : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B) (hd : 0 < d) :
    0 < exceptionalLowWidth N Q B d := by unfold exceptionalLowWidth;positivity

theorem exceptionalLowWidth_le_square {N Q B d : ℝ} (hQ : 0 < Q) (hd : B*d ≤ Q) :
    exceptionalLowWidth N Q B d ≤ N^2 := by
  unfold exceptionalLowWidth
  apply (div_le_iff₀ hQ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg N)]

theorem exceptionalLowWidth_cancel {N Q B d : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B) (hd : 0 < d) :
    B/(exceptionalLowWidth N Q B d)=Q/(d*N^2) := by
  unfold exceptionalLowWidth
  field_simp

end PrimeSquares
