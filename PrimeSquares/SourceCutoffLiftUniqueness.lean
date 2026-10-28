import PrimeSquares.CanonicalLiftArcUniqueness
import PrimeSquares.SourceArcCutoff
namespace PrimeSquares
theorem source_cutoff_lift_unique {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (ξ : ℝ) (k l : ℤ)
    (hkr : sourceArcCutoffScale s (ξ-(r : ℝ)+(k : ℝ)) ≠ 0)
    (hlt : sourceArcCutoffScale s (ξ-(t : ℝ)+(l : ℝ)) ≠ 0) : r=t :=
  canonical_lift_small_arc_unique hr ht hrD htD (dyadic_cutoff_width hs) k l
    (sourceArcCutoffScale_radius s hkr).le (sourceArcCutoffScale_radius s hlt).le
end PrimeSquares
