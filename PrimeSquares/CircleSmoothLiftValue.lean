import PrimeSquares.CircleSmoothCutoff
import PrimeSquares.ScaledSmoothSingleLift
namespace PrimeSquares
theorem circleSmoothCutoff_eq_lift {a : ℝ} (ha : 1 ≤ a) (h4 : 4 ≤ a) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoff (a*(ξ-(r : ℝ)+k)) ≠ 0) :
    circleSmoothCutoff a ha r (ξ : PrimeCircle)=Complex.ofReal (sourceArcCutoff (a*(ξ-(r : ℝ)+k))) := by
  rw [circleSmoothCutoff_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoff (a*(ξ-(r : ℝ)+l))=0 := by
    by_contra h
    exact hl (scaledSmoothCutoff_single_lift h4 r ξ l k h hk)
  rw [hz,Complex.ofReal_zero]
end PrimeSquares
