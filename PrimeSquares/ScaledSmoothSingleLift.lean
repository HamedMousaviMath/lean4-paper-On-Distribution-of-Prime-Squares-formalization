import PrimeSquares.ScaledSmoothCutoffMap
namespace PrimeSquares
theorem scaledSmoothCutoff_single_lift {a : ℝ} (ha : 4 ≤ a) (r : ℚ) (ξ : ℝ) (k l : ℤ)
    (hk : sourceArcCutoff (a*(ξ-(r : ℝ)+k)) ≠ 0)
    (hl : sourceArcCutoff (a*(ξ-(r : ℝ)+l)) ≠ 0) : k=l := by
  by_contra hne
  have hp : 0 < a := by linarith
  have hb := integer_cast_abs_one_le (sub_ne_zero.mpr hne)
  have hkr := scaledSmoothCutoff_radius hp hk
  have hlr := scaledSmoothCutoff_radius hp hl
  have he : ((k-l : ℤ) : ℝ)=(ξ-(r : ℝ)+(k : ℝ))-(ξ-(r : ℝ)+(l : ℝ)) := by push_cast;ring
  rw [he] at hb
  have hd := abs_sub (ξ-(r : ℝ)+(k : ℝ)) (ξ-(r : ℝ)+(l : ℝ))
  have hw : 2*(1/a) < 1 := by
    rw [mul_one_div]
    exact (div_lt_iff₀ hp).mpr (by linarith)
  linarith
end PrimeSquares
