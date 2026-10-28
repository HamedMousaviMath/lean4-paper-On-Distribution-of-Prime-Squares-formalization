import PrimeSquares.PureCollarOnset

namespace PrimeSquares

noncomputable def annularCollarFactor (N : ℕ) (β q Q θ : ℝ) : ℂ :=
  annularOscillatoryModel N β θ*Complex.ofReal (annularCollarMask N q Q θ)

theorem annularCollarFactor_le_annular (N : ℕ) (β q Q θ : ℝ) :
    ‖annularCollarFactor N β q Q θ‖ ≤ ‖annularOscillatoryModel N β θ‖ := by
  rw [annularCollarFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annularCollarMask_range N q Q θ).1]
  exact (mul_le_mul_of_nonneg_left (annularCollarMask_range N q Q θ).2 (norm_nonneg _)).trans (by simp)

theorem annularCollarFactor_zero_of_mask (N : ℕ) (β q Q θ : ℝ) (hz : annularCollarMask N q Q θ=0) :
    annularCollarFactor N β q Q θ=0 := by simp only [annularCollarFactor,hz,Complex.ofReal_zero,mul_zero]

theorem annularHighFactor_eq_collar {N : ℕ} {β q Q θ : ℝ} (hq : q ≤ Q) :
    annularHighFactor N β q Q θ=annularCollarFactor N β q Q θ := by
  simp only [annularHighFactor,annularCollarFactor,annularHighMask_eq_collar hq]

end PrimeSquares
