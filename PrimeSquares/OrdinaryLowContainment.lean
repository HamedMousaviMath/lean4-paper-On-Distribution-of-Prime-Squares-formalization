import PrimeSquares.NarrowCutoffContainment
import PrimeSquares.FiniteMajorArcModels

namespace PrimeSquares

theorem ordinaryNarrowCutoff_mul_broad {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {Q R ξ : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) :
    ordinaryNarrowCutoff N Q r ξ *
      Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))) =
      ordinaryNarrowCutoff N Q r ξ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hs : (2 : ℝ)^(Nat.log2 r.den) ≤ (r.den : ℝ) := by
    exact_mod_cast Nat.log2_self_le r.den_pos.ne'
  have h := narrowCutoff_mul_broad (θ := ξ-(r : ℝ)) hNp hdp hQ hr hQR hs hb
  simpa only [ordinaryNarrowCutoff,Complex.ofReal_mul] using congrArg Complex.ofReal h

end PrimeSquares
