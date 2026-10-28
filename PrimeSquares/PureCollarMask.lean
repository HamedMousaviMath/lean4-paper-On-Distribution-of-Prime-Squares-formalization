import PrimeSquares.DyadicNarrowWidths

namespace PrimeSquares

noncomputable def annularCollarMask (N q Q θ : ℝ) : ℝ :=
  1-sourceArcCutoff ((q*N^2/Q)*θ)

theorem annularCollarMask_range (N q Q θ : ℝ) :
    0 ≤ annularCollarMask N q Q θ ∧ annularCollarMask N q Q θ ≤ 1 :=
  ⟨sub_nonneg.mpr (sourceArcCutoff_le_one _),sub_le_self _ (sourceArcCutoff_nonneg _)⟩

theorem annularCollarMask_at_zero (N q Q : ℝ) : annularCollarMask N q Q 0=0 := by
  simp only [annularCollarMask,mul_zero,sourceArcCutoff_core (by norm_num : |(0 : ℝ)| ≤ 1/2),sub_self]

theorem annularHighMask_eq_collar {N q Q θ : ℝ} (hq : q ≤ Q) :
    annularHighMask N q Q θ=annularCollarMask N q Q θ := by
  simp only [annularHighMask,annularCollarMask,ite_eq_left hq]

end PrimeSquares
