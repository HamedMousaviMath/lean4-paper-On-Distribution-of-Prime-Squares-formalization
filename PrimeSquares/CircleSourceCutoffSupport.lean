import PrimeSquares.CircleSourceCutoffLiftValue
namespace PrimeSquares
theorem circleSourceCutoff_ne_zero_of_lift {s : ℕ} (hs : 1 ≤ s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0) :
    circleSourceCutoff s r (ξ : PrimeCircle) ≠ 0 := by
  rw [circleSourceCutoff_eq_lift hs r ξ k hk]
  exact_mod_cast hk
end PrimeSquares
