import PrimeSquares.RationalArcSeparation
namespace PrimeSquares
theorem canonical_lift_denominator_bound {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1)
    (hne : r ≠ t) {D : ℝ} (hrD : (r.den : ℝ) ≤ D) (htD : (t.den : ℝ) ≤ D) (k : ℤ) :
    1/D^2 ≤ |(r : ℝ)-(t : ℝ)-(k : ℝ)| := by
  have hrd : (0 : ℝ)<r.den := by exact_mod_cast r.den_pos
  have htd : (0 : ℝ)<t.den := by exact_mod_cast t.den_pos
  have hprod : (r.den : ℝ)*t.den ≤ D^2 := by
    have hD := hrd.trans_le hrD
    nlinarith
  exact (one_div_le_one_div_of_le (mul_pos hrd htd) hprod).trans
    (rational_canonical_lifts_separation r t hr ht hne k)
end PrimeSquares
