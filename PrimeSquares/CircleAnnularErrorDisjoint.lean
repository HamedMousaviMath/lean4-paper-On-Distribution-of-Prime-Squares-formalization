import PrimeSquares.CircleAnnularErrorSupport
import PrimeSquares.CircleSourceCutoffDisjoint
namespace PrimeSquares
theorem circleAnnularProjectionError_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hrt : r ≠ t)
    (hd : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (he : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (β γ : ℝ) (θ : PrimeCircle) :
    circleAnnularProjectionError N hN β s r θ=0 ∨ circleAnnularProjectionError M hM γ s t θ=0 := by
  rcases circleSourceCutoff_disjoint hs hr ht hrt hd he θ with h | h
  · exact Or.inl (circleAnnularProjectionError_cutoff_zero N hN β (by omega) r θ h)
  · exact Or.inr (circleAnnularProjectionError_cutoff_zero M hM γ (by omega) t θ h)
end PrimeSquares
