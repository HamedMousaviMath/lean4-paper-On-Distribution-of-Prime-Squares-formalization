import PrimeSquares.CollarFrequencyContinuity
import PrimeSquares.CenteredLowSymbol

namespace PrimeSquares

noncomputable def annularCollarSymbol (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) : C(ℝ,ℂ) :=
  ⟨fun θ => annularCollarFactor N β q Q θ*Complex.ofReal (sourceArcCutoffScale s θ),
    (annularCollarFactor_continuous N hN β q Q).mul (Complex.continuous_ofReal.comp
      (sourceArcCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id)))⟩

theorem annularCollarSymbol_le_factor (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (θ : ℝ) :
    ‖annularCollarSymbol N hN β q Q s θ‖ ≤ ‖annularCollarFactor N β q Q θ‖ := by
  change ‖annularCollarFactor N β q Q θ*Complex.ofReal (sourceArcCutoffScale s θ)‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans (by simp)

end PrimeSquares
