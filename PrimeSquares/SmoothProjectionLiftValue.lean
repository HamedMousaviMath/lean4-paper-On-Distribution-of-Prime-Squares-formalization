import PrimeSquares.CircleAnnularSmoothProjection
import PrimeSquares.SourceCutoffSingleLift
namespace PrimeSquares
theorem circleAnnularSmoothProjection_eq_lift (N : ℕ) {s : ℕ} (hs : 1 ≤ s)
    (r : ℚ) (ξ : ℝ) (k : ℤ) (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0) :
    circleAnnularSmoothProjection N s r (ξ : PrimeCircle)=
      Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*(ξ-(r : ℝ)+k)))*
        Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  rw [circleAnnularSmoothProjection_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoffScale s (ξ-(r : ℝ)+l)=0 := by
    by_contra h
    exact hl (source_cutoff_single_lift hs r ξ l k h hk)
  rw [hz,Complex.ofReal_zero,mul_zero]
end PrimeSquares
