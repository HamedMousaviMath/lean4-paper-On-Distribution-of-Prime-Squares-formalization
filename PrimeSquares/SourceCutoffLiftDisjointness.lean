import PrimeSquares.SourceCutoffLiftUniqueness
namespace PrimeSquares
theorem source_cutoff_lift_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (ξ : ℝ) (k l : ℤ) :
    sourceArcCutoffScale s (ξ-(r : ℝ)+(k : ℝ))=0 ∨
    sourceArcCutoffScale s (ξ-(t : ℝ)+(l : ℝ))=0 := by
  by_cases hk : sourceArcCutoffScale s (ξ-(r : ℝ)+(k : ℝ))=0
  · exact Or.inl hk
  · right
    by_contra hl
    exact hne (source_cutoff_lift_unique hs hr ht hrD htD ξ k l hk hl)
end PrimeSquares
