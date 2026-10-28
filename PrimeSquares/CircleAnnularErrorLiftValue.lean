import PrimeSquares.CircleAnnularProjectionError
import PrimeSquares.SourceCutoffSingleLift
namespace PrimeSquares
theorem circleAnnularProjectionError_eq_lift (N : ℕ) (hN : 1 ≤ N) (β : ℝ) {s : ℕ}
    (hs : 1 ≤ s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0) :
    circleAnnularProjectionError N hN β s r (ξ : PrimeCircle)=
      annularProjectionError N β (ξ-(r : ℝ)+k)*
        Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  rw [circleAnnularProjectionError_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoffScale s (ξ-(r : ℝ)+l)=0 := by
    by_contra h
    exact hl (source_cutoff_single_lift hs r ξ l k h hk)
  rw [hz,Complex.ofReal_zero,mul_zero]
end PrimeSquares
