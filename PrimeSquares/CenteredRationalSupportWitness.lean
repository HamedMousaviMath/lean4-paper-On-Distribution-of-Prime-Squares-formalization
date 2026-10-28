import PrimeSquares.CenteredRationalSymbol
namespace PrimeSquares
theorem centeredRationalSymbol_cutoff_zero (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (x : ℝ)
    (h : sourceArcCutoffScale (Nat.log2 r.den) x=0) :
    centeredRationalSymbol N hN χ κ β r x=0 := by
  simp only [centeredRationalSymbol,ContinuousMap.coe_mk,localizedAnnularGaussModel,h,
    Complex.ofReal_zero,mul_zero]
end PrimeSquares
