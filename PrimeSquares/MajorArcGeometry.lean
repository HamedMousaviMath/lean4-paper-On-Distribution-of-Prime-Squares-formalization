import PrimeSquares.SourceArcCutoff
import PrimeSquares.CircleFourier

namespace PrimeSquares

theorem rationalMajorArc_unique {r t : ℚ} {ξ R N : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hsep : 2*R^3 < N^2)
    (hr : (r.den : ℝ) ≤ R) (ht : (t.den : ℝ) ≤ R)
    (hξr : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*N^2))
    (hξt : |ξ-(t : ℝ)| ≤ R/((t.den : ℝ)*N^2)) : r = t := by
  have hwidth : 2*(R/N^2) < 1/R^2 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (sq_pos_of_pos hN) (sq_pos_of_pos hR)]
    nlinarith only [hsep]
  have hrd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have htd : (1 : ℝ) ≤ t.den := by exact_mod_cast t.den_pos
  have hradius : R/((r.den : ℝ)*N^2) ≤ R/N^2 :=
    div_le_div_of_nonneg_left hR.le (sq_pos_of_pos hN) (by nlinarith [sq_nonneg N])
  have tradius : R/((t.den : ℝ)*N^2) ≤ R/N^2 :=
    div_le_div_of_nonneg_left hR.le (sq_pos_of_pos hN) (by nlinarith [sq_nonneg N])
  exact rational_small_arc_unique hr ht hwidth (hξr.trans hradius) (hξt.trans tradius)

theorem rationalMajorArc_other_outside {r t : ℚ} {ξ R N : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hsep : 2*R^3 < N^2)
    (hr : (r.den : ℝ) ≤ R) (ht : (t.den : ℝ) ≤ R) (hne : t ≠ r)
    (hξr : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*N^2)) :
    R/((t.den : ℝ)*N^2) < |ξ-(t : ℝ)| := by
  by_contra h
  exact hne (rationalMajorArc_unique hR hN hsep ht hr (le_of_not_gt h) hξr)

theorem rationalMajorArc_cutoff_core {N : ℕ} (hN : 1 ≤ N) {r : ℚ} {R ξ : ℝ}
    (hden : (r.den : ℝ) ≤ R) (hbudget : 2*R^4 ≤ (N : ℝ)^2)
    (hξ : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*(N : ℝ)^2)) :
    sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) = 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hs : (2 : ℝ)^(Nat.log2 r.den) ≤ (r.den : ℝ) := by
    exact_mod_cast Nat.log2_self_le r.den_pos.ne'
  exact sourceArcCutoffScale_major_arc hNp hdp hden hs hbudget hξ

theorem rationalCenter_add_offset (r : ℚ) (ξ : ℝ) :
    ((((r.num : ℝ)/r.den : ℝ) : PrimeCircle) + ((ξ-(r : ℝ) : ℝ) : PrimeCircle)) =
      (ξ : PrimeCircle) := by
  rw [← AddCircle.coe_add]
  congr 1
  rw [← Rat.cast_def]
  ring

end PrimeSquares
