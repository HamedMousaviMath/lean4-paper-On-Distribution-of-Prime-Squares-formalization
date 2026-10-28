import PrimeSquares.SourceCutoffLiftWidth
namespace PrimeSquares
theorem source_cutoff_single_lift {s : ℕ} (hs : 1 ≤ s) (r : ℚ) (ξ : ℝ) (k l : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+(k : ℝ)) ≠ 0)
    (hl : sourceArcCutoffScale s (ξ-(r : ℝ)+(l : ℝ)) ≠ 0) : k=l := by
  by_contra hne
  have hb := integer_cast_abs_one_le (sub_ne_zero.mpr hne)
  have hkr := sourceArcCutoffScale_radius s hk
  have hlr := sourceArcCutoffScale_radius s hl
  have he : ((k-l : ℤ) : ℝ)=(ξ-(r : ℝ)+(k : ℝ))-(ξ-(r : ℝ)+(l : ℝ)) := by push_cast;ring
  rw [he] at hb
  have hd := abs_sub (ξ-(r : ℝ)+(k : ℝ)) (ξ-(r : ℝ)+(l : ℝ))
  have hw := source_cutoff_lift_width hs
  linarith
end PrimeSquares
