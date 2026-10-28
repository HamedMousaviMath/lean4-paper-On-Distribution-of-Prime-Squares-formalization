import PrimeSquares.CircleRationalModel
import PrimeSquares.CenteredRationalSupportWitness
namespace PrimeSquares
theorem circleRationalModel_nonzero_cutoff_lift (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ)
    (h : circleRationalModelTerm N hN χ κ β r (ξ : PrimeCircle) ≠ 0) :
    ∃ k : ℤ, sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)+k) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  rw [circleRationalModelTerm_real]
  have hz : ∀ k : ℤ, centeredRationalSymbol N hN χ κ β r (ξ-(r : ℝ)+k)=0 :=
    fun k => centeredRationalSymbol_cutoff_zero N hN χ κ β r _ (hn k)
  simp only [hz,tsum_zero]
end PrimeSquares
