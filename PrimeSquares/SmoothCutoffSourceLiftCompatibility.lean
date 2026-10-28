import PrimeSquares.CircleSmoothCutoff
import PrimeSquares.SourceCutoffLiftWidth
namespace PrimeSquares
theorem smoothCutoff_source_lifts_unique {a : ℝ} (ha : 4 ≤ a) {s : ℕ} (hs : 1 ≤ s)
    (r : ℚ) (ξ : ℝ) (k l : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0)
    (hl : sourceArcCutoff (a*(ξ-(r : ℝ)+l)) ≠ 0) : k=l := by
  by_contra hne
  have hp : 0 < a := by linarith
  have hb := integer_cast_abs_one_le (sub_ne_zero.mpr hne)
  have hkr := sourceArcCutoffScale_radius s hk
  have hlr := scaledSmoothCutoff_radius hp hl
  have he : ((k-l : ℤ) : ℝ)=(ξ-(r : ℝ)+(k : ℝ))-(ξ-(r : ℝ)+(l : ℝ)) := by push_cast;ring
  rw [he] at hb
  have hd := abs_sub (ξ-(r : ℝ)+(k : ℝ)) (ξ-(r : ℝ)+(l : ℝ))
  have hw := source_cutoff_lift_width hs
  have hr : 1/a ≤ 1/4 := (div_le_iff₀ hp).mpr (by linarith)
  linarith
theorem circleSmoothCutoff_on_source_lift {a : ℝ} (ha : 1 ≤ a) (h4 : 4 ≤ a) {s : ℕ}
    (hs : 1 ≤ s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0) :
    circleSmoothCutoff a ha r (ξ : PrimeCircle)=Complex.ofReal (sourceArcCutoff (a*(ξ-(r : ℝ)+k))) := by
  rw [circleSmoothCutoff_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoff (a*(ξ-(r : ℝ)+l))=0 := by
    by_contra h
    exact hl (smoothCutoff_source_lifts_unique h4 hs r ξ k l hk h).symm
  rw [hz,Complex.ofReal_zero]
end PrimeSquares
