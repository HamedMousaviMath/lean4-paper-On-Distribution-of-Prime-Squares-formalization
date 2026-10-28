import PrimeSquares.CircleSourceCutoffWitness
import PrimeSquares.SourceCutoffLiftDisjointness
namespace PrimeSquares
theorem circleSourceCutoff_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (θ : PrimeCircle) : circleSourceCutoff s r θ=0 ∨ circleSourceCutoff s t θ=0 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [← he]
  by_cases hk : circleSourceCutoff s r (ξ : PrimeCircle)=0
  · exact Or.inl hk
  · right
    by_contra hl
    obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hk
    obtain ⟨l,hl⟩ := circleSourceCutoff_nonzero_lift ξ hl
    exact (source_cutoff_lift_disjoint hs hr ht hne hrD htD ξ k l).elim hk hl
end PrimeSquares
