import PrimeSquares.CircleRationalModelSupport
import PrimeSquares.CircleSourceCutoffDisjoint
namespace PrimeSquares
theorem circleRationalModel_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hrs : Nat.log2 r.den=s) (hts : Nat.log2 t.den=s)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (χ ψ : ∀ a : ℚ, DirichletCharacter ℂ a.den) (κ μ : ℚ → ℂ) (β γ : ℝ)
    (θ : PrimeCircle) :
    circleRationalModelTerm N hN χ κ β r θ=0 ∨
    circleRationalModelTerm M hM ψ μ γ t θ=0 := by
  by_cases h : circleRationalModelTerm N hN χ κ β r θ=0
  · exact Or.inl h
  · right
    by_contra hn
    have ha := circleRationalModel_cutoff_nonzero N hN χ κ β r (by omega) θ h
    have hb := circleRationalModel_cutoff_nonzero M hM ψ μ γ t (by omega) θ hn
    rw [hrs] at ha
    rw [hts] at hb
    exact (circleSourceCutoff_disjoint hs hr ht hne hrD htD θ).elim ha hb
end PrimeSquares
