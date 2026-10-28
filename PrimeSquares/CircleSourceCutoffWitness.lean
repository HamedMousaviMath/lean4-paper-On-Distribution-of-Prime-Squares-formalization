import PrimeSquares.CircleSourceCutoff
namespace PrimeSquares
theorem circleSourceCutoff_nonzero_lift {s : ℕ} {r : ℚ} (ξ : ℝ)
    (h : circleSourceCutoff s r (ξ : PrimeCircle) ≠ 0) :
    ∃ k : ℤ, sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  rw [circleSourceCutoff_real]
  simp only [hn,Complex.ofReal_zero,tsum_zero]
end PrimeSquares
