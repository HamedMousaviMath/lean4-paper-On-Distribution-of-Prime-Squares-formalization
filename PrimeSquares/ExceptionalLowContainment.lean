import PrimeSquares.OrdinaryLowContainment

namespace PrimeSquares

theorem exceptionalNarrowCutoff_mul_broad {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) {Q B₀ R ξ : ℝ} (hQ : 0 < Q) (hB₀ : 0 < B₀)
    (hWR : Q*(q₀ : ℝ)/B₀ ≤ R) (hr : (r.den : ℝ) ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) :
    exceptionalNarrowCutoff N q₀ Q B₀ r ξ *
      Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))) =
      exceptionalNarrowCutoff N q₀ Q B₀ r ξ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq₀p : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hW : 0 < Q*(q₀ : ℝ)/B₀ := by positivity
  have hs : (2 : ℝ)^(Nat.log2 r.den) ≤ (r.den : ℝ) := by
    exact_mod_cast Nat.log2_self_le r.den_pos.ne'
  have ha : B₀*((r.den : ℝ)/q₀)*(N : ℝ)^2/Q =
      (r.den : ℝ)*(N : ℝ)^2/(Q*(q₀ : ℝ)/B₀) := by field_simp
  have h := narrowCutoff_mul_broad (θ := ξ-(r : ℝ)) hNp hdp hW hr hWR hs hb
  simpa only [exceptionalNarrowCutoff,ha,Complex.ofReal_mul] using congrArg Complex.ofReal h

end PrimeSquares
