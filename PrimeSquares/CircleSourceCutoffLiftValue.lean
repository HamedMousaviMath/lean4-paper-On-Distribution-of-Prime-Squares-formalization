import PrimeSquares.CircleSourceCutoff
import PrimeSquares.SourceCutoffSingleLift
namespace PrimeSquares
theorem circleSourceCutoff_eq_lift {s : ℕ} (hs : 1 ≤ s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0) :
    circleSourceCutoff s r (ξ : PrimeCircle)=
      Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  rw [circleSourceCutoff_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoffScale s (ξ-(r : ℝ)+l)=0 := by
    by_contra h
    exact hl (source_cutoff_single_lift hs r ξ l k h hk)
  rw [hz,Complex.ofReal_zero]
end PrimeSquares
