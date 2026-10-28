import PrimeSquares.SharpHighExponentWeight
namespace PrimeSquares
theorem sharpHigh_polynomial_absorption {ε : ℝ} (hε : 0 < ε) (m : ℝ) :
    ∃ D : ℝ,0 < D ∧ ∀ L : ℝ,2 ≤ L → L^m ≤ D*Real.exp (ε*sharpHighExponentWeight L) := by
  obtain ⟨D,hD,h⟩ := rpow_le_exp_orliczWeight (by norm_num : (0 : ℝ) < 1/2) hε m
  refine ⟨D,hD,?_⟩
  intro L hL
  exact (h L hL).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (orliczWeight_le_sharpHighExponentWeight hL) hε.le)) hD.le)
end PrimeSquares
