import PrimeSquares.CircleRationalModelWitness
import PrimeSquares.CircleSourceCutoffSupport
namespace PrimeSquares
theorem circleRationalModel_cutoff_nonzero (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ)
    (hs : 1 ≤ Nat.log2 r.den) (θ : PrimeCircle)
    (h : circleRationalModelTerm N hN χ κ β r θ ≠ 0) :
    circleSourceCutoff (Nat.log2 r.den) r θ ≠ 0 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [← he] at h ⊢
  obtain ⟨k,hk⟩ := circleRationalModel_nonzero_cutoff_lift N hN χ κ β r ξ h
  exact circleSourceCutoff_ne_zero_of_lift hs r ξ k hk
end PrimeSquares
