import PrimeSquares.CenteredHighSymbol
import PrimeSquares.CompactLowSourceIdentification

namespace PrimeSquares

theorem centeredHighSymbol_source {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) {Q B₀ R ξ : ℝ} (hQ : 0 < Q) (hB₀ : 0 < B₀)
    (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/B₀ ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    centeredHighSymbol N hN q₀ Q B₀ χ κ β r (ξ-(r : ℝ)) =
      rationalHighModelTerm N q₀ Q B₀ χ κ β r ξ := by
  simp only [centeredHighSymbol,ContinuousMap.sub_apply]
  rw [centeredRationalSymbol_translate,
    centeredLowSymbol_source hN r hq₀ hQ hB₀ hQR hWR hr hb χ κ β]
  rw [←rationalModel_low_add_high N q₀ Q B₀ χ κ β r ξ]
  exact add_sub_cancel_left _ _

end PrimeSquares
