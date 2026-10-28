import PrimeSquares.CircleSmoothSupportWitness
import PrimeSquares.SourceCutoffLiftUniqueness
namespace PrimeSquares
theorem source_smooth_cross_lift_unique {s : ℕ} (hs : 2 ≤ s) {a : ℝ}
    (ha : (16 : ℝ)^s ≤ a) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (ξ : ℝ) (k l : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k) ≠ 0)
    (hl : sourceArcCutoff (a*(ξ-(t : ℝ)+l)) ≠ 0) : r=t := by
  have hp : 0 < a := lt_of_lt_of_le (by positivity : 0 < (16 : ℝ)^s) ha
  have hw : 1/a ≤ 1/(16 : ℝ)^s := one_div_le_one_div_of_le (by positivity) ha
  exact canonical_lift_small_arc_unique hr ht hrD htD (dyadic_cutoff_width hs) k l
    (sourceArcCutoffScale_radius s hk).le ((scaledSmoothCutoff_radius hp hl).le.trans hw)
end PrimeSquares
