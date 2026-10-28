import PrimeSquares.CenteredLowSymbol
import PrimeSquares.ExceptionalLowContainment

namespace PrimeSquares

theorem centeredLowSymbol_source {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) {Q B₀ R ξ : ℝ} (hQ : 0 < Q) (hB₀ : 0 < B₀)
    (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/B₀ ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    centeredLowSymbol N hN q₀ Q B₀ χ κ β r (ξ-(r : ℝ)) =
      rationalLowModelTerm N q₀ Q B₀ χ κ β r ξ := by
  have ho := ordinaryNarrowCutoff_mul_broad hN r (ξ := ξ) hQ hQR hr hb
  have he := exceptionalNarrowCutoff_mul_broad hN r (ξ := ξ) hq₀ hQ hB₀ hWR hr hb
  change rationalLowModelTerm N q₀ Q B₀ χ κ β r (ξ-(r : ℝ)+(r : ℝ))*
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))) = _
  rw [sub_add_cancel]
  simp only [rationalLowModelTerm,add_mul,ite_mul,mul_assoc,ho,he,zero_mul]

end PrimeSquares
