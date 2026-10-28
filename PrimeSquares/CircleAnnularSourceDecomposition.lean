import PrimeSquares.CircleAnnularProjectionIdentity
namespace PrimeSquares
theorem circleAnnularSource_decomposition (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) (r : ℚ) :
    circleAnnularSource N hN β s r=
      annularOscillatoryModel N β 0 • circleAnnularSmoothProjection N s r+
        circleAnnularProjectionError N hN β s r := by
  have h := circleAnnularProjectionError_identity N hN β s r
  rw [eq_sub_iff_add_eq] at h
  simpa only [add_comm] using h.symm
end PrimeSquares
