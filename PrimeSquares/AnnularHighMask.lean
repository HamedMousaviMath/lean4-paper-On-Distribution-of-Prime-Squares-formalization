import PrimeSquares.NarrowCollarOnset

namespace PrimeSquares

noncomputable def annularHighMask (N q W θ : ℝ) : ℝ :=
  1-(if q ≤ W then sourceArcCutoff ((q*N^2/W)*θ) else 0)

theorem annularHighMask_range (N q W θ : ℝ) :
    0 ≤ annularHighMask N q W θ ∧ annularHighMask N q W θ ≤ 1 := by
  classical
  unfold annularHighMask
  split_ifs
  · exact ⟨sub_nonneg.mpr (sourceArcCutoff_le_one _),sub_le_self _ (sourceArcCutoff_nonneg _)⟩
  · norm_num

theorem annularHighMask_onset {N q W θ : ℝ} (hN : 0 < N) (hq : 0 < q) (hW : 0 < W)
    (hql : q ≤ W) (hn : annularHighMask N q W θ ≠ 0) : W/(2*q*N^2) < |θ| := by
  apply ordinary_collar_frequency_lower (b := 1) hW hq hN (by ring)
  simpa only [annularHighMask,ite_eq_left hql] using hn

end PrimeSquares
