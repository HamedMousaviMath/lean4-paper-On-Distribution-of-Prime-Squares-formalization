import PrimeSquares.CircleSourceCutoffDisjoint
namespace PrimeSquares
theorem circleSourceCutoff_mul_eq_zero {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    circleSourceCutoff s r * circleSourceCutoff s t=0 := by
  ext θ
  rcases circleSourceCutoff_disjoint hs hr ht hne hrD htD θ with h | h
  · simp [h]
  · simp [h]
end PrimeSquares
