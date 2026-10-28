import PrimeSquares.ConductorMultiplePrefix
import PrimeSquares.OrliczGrowth
namespace PrimeSquares
noncomputable def sharpHighExponentWeight (L : ℝ) : ℝ := Real.sqrt L/Real.log L
theorem sharpHighExponentWeight_pos {L : ℝ} (hL : 2 ≤ L) : 0 < sharpHighExponentWeight L := by
  exact div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))
theorem orliczWeight_le_sharpHighExponentWeight {L : ℝ} (hL : 2 ≤ L) :
    orliczWeight (1/2) L ≤ sharpHighExponentWeight L := by
  rw [orliczWeight,sharpHighExponentWeight,←Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.log_pos (by linarith)) (by linarith)
end PrimeSquares
