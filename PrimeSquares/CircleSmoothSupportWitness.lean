import PrimeSquares.CircleSmoothCutoff
namespace PrimeSquares
theorem circleSmoothCutoff_nonzero_lift {a : ℝ} (ha : 1 ≤ a) (r : ℚ) (ξ : ℝ)
    (hn : circleSmoothCutoff a ha r (ξ : PrimeCircle) ≠ 0) :
    ∃ k : ℤ,sourceArcCutoff (a*(ξ-(r : ℝ)+k)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hn
  rw [circleSmoothCutoff_real]
  simp only [h,Complex.ofReal_zero,tsum_zero]
end PrimeSquares
