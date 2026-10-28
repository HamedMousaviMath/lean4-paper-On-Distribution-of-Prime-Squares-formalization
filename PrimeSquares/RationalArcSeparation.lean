import PrimeSquares.MajorArcParameters
import Mathlib.Data.Rat.Cast.Order

/-!
# Exact rational separation, including integer lifts on the circle
-/

namespace PrimeSquares

theorem integer_cast_abs_one_le {d : ℤ} (hd : d ≠ 0) :
    (1 : ℝ) ≤ |(d : ℝ)| := by
  have hp : (0 : ℤ) < |d| := abs_pos.mpr hd
  have hi : (1 : ℤ) ≤ |d| := by omega
  exact_mod_cast hi

theorem rational_fraction_separation (a b : ℤ) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hcross : a * (r : ℤ) - b * (q : ℤ) ≠ 0) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ)/q - (b : ℝ)/r| := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have he : ((a * (r : ℤ) - b * (q : ℤ) : ℤ) : ℝ) =
      ((a : ℝ)/q - (b : ℝ)/r) * ((q : ℝ)*r) := by
    push_cast
    field_simp
  have hb := integer_cast_abs_one_le hcross
  rw [he, abs_mul, abs_of_pos (mul_pos hqp hrp)] at hb
  exact (div_le_iff₀ (mul_pos hqp hrp)).mpr hb

theorem rational_separation (r s : ℚ) (hne : r ≠ s) :
    1 / ((r.den : ℝ) * s.den) ≤ |(r : ℝ) - (s : ℝ)| := by
  have hrc : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsc : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hreal : (r : ℝ) ≠ (s : ℝ) := by exact_mod_cast hne
  have hc : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 := by
    intro h
    apply hreal
    rw [Rat.cast_def, Rat.cast_def]
    apply (div_eq_div_iff hrc.ne' hsc.ne').mpr
    exact_mod_cast sub_eq_zero.mp h
  simpa only [Rat.cast_def] using
    rational_fraction_separation r.num s.num r.den_pos s.den_pos hc

theorem rational_canonical_lifts_separation (r s : ℚ)
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hne : r ≠ s) (k : ℤ) :
    1 / ((r.den : ℝ) * s.den) ≤ |(r : ℝ) - (s : ℝ) - (k : ℝ)| := by
  have hneq : r ≠ s + (k : ℚ) := by
    intro heq
    have hkL : (-1 : ℚ) < (k : ℚ) := by linarith [hr.1, hs.2]
    have hkU : (k : ℚ) < 1 := by linarith [hr.2, hs.1]
    have hkLi : (-1 : ℤ) < k := by exact_mod_cast hkL
    have hkUi : k < (1 : ℤ) := by exact_mod_cast hkU
    have hk : k = 0 := by omega
    apply hne
    simpa only [hk, Int.cast_zero, add_zero] using heq
  have h := rational_separation r (s + (k : ℚ)) hneq
  simpa only [Rat.add_intCast_den, Rat.cast_add, Rat.cast_intCast,
    sub_add_eq_sub_sub] using h

theorem rational_separation_den_bound {r s : ℚ} (hne : r ≠ s)
    {D : ℝ} (hr : (r.den : ℝ) ≤ D) (hs : (s.den : ℝ) ≤ D) :
    1 / D^2 ≤ |(r : ℝ) - (s : ℝ)| := by
  have hrd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsd : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hD : 0 < D := hrd.trans_le hr
  have hp : (r.den : ℝ) * s.den ≤ D^2 := by nlinarith
  exact (one_div_le_one_div_of_le (mul_pos hrd hsd) hp).trans
    (rational_separation r s hne)

theorem rational_small_arc_unique {r s : ℚ} {ξ δ D : ℝ}
    (hr : (r.den : ℝ) ≤ D) (hs : (s.den : ℝ) ≤ D)
    (hwidth : 2*δ < 1/D^2)
    (hξr : |ξ - (r : ℝ)| ≤ δ) (hξs : |ξ - (s : ℝ)| ≤ δ) : r = s := by
  by_contra hne
  have hsep := rational_separation_den_bound hne hr hs
  have hdist : |(r : ℝ) - (s : ℝ)| ≤ 2*δ := by
    calc
      _ ≤ |(r : ℝ)-ξ| + |ξ-(s : ℝ)| := abs_sub_le _ _ _
      _ = |ξ-(r : ℝ)| + |ξ-(s : ℝ)| := by rw [abs_sub_comm (r : ℝ) ξ]
      _ ≤ δ+δ := add_le_add hξr hξs
      _ = _ := by ring
  linarith

end PrimeSquares
