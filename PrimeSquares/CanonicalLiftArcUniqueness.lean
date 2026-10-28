import PrimeSquares.CanonicalLiftDenominatorBound
namespace PrimeSquares
theorem canonical_lift_small_arc_unique {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1)
    {D δ ξ : ℝ} (hrD : (r.den : ℝ) ≤ D) (htD : (t.den : ℝ) ≤ D)
    (hw : 2*δ < 1/D^2) (k l : ℤ)
    (hkr : |ξ-(r : ℝ)+(k : ℝ)| ≤ δ) (hlt : |ξ-(t : ℝ)+(l : ℝ)| ≤ δ) : r=t := by
  by_contra hne
  have hs := canonical_lift_denominator_bound hr ht hne hrD htD (k-l)
  have he : (r : ℝ)-(t : ℝ)-((k-l : ℤ) : ℝ)=
      (ξ-(t : ℝ)+(l : ℝ))-(ξ-(r : ℝ)+(k : ℝ)) := by push_cast;ring
  rw [he] at hs
  have hdist := abs_sub (ξ-(t : ℝ)+(l : ℝ)) (ξ-(r : ℝ)+(k : ℝ))
  linarith
end PrimeSquares
