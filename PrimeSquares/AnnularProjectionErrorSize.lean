import PrimeSquares.AnnularProjectionError
namespace PrimeSquares
theorem annularProjectionError_norm_one {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : β ≤ 1) (θ : ℝ) :
    ‖annularProjectionError N β θ‖ ≤ 1 := by
  have hb : ‖Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*θ))‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact sourceArcCutoff_le_one _
  calc
    _ ≤ ‖annularOscillatoryModel N β θ‖+
      ‖annularOscillatoryModel N β 0*Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*θ))‖ := norm_sub_le _ _
    _ ≤ 1/2+(1/2 : ℝ)*1 := by
      rw [norm_mul]
      exact add_le_add (annularOscillatoryModel_norm_half hN hβ θ)
        (mul_le_mul (annularOscillatoryModel_norm_half hN hβ 0) hb (norm_nonneg _) (by norm_num))
    _ = 1 := by norm_num
end PrimeSquares
