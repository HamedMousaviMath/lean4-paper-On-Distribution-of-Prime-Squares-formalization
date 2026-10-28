import PrimeSquares.SourceArcCutoff

namespace PrimeSquares

theorem dilatedSourceCutoff_radius {A θ : ℝ} (hA : 0 < A)
    (h : sourceArcCutoff (A*θ) ≠ 0) : |θ| < 1/A := by
  have hr := sourceArcCutoff_radius h
  rw [abs_mul, abs_of_pos hA] at hr
  exact (lt_div_iff₀ hA).mpr (by nlinarith)

theorem dilatedSourceCutoff_core {A θ : ℝ} (hA : 0 < A)
    (h : |θ| ≤ 1/(2*A)) : sourceArcCutoff (A*θ) = 1 := by
  apply sourceArcCutoff_core
  rw [abs_mul, abs_of_pos hA]
  have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 2*A)).mp h
  nlinarith

end PrimeSquares
