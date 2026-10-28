import PrimeSquares.SourceCircleDoubleSum
import PrimeSquares.CompactLowSourceIdentification

namespace PrimeSquares

theorem centeredLowSymbol_bare {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) {Q B₀ R : ℝ} (hQ : 0 < Q) (hB₀ : 0 < B₀)
    (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/B₀ ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β θ : ℝ) :
    centeredLowSymbol N hN q₀ Q B₀ χ κ β r θ=
      rationalLowModelTerm N q₀ Q B₀ χ κ β r (θ+(r : ℝ)) := by
  simpa only [add_sub_cancel_right] using
    centeredLowSymbol_source hN r hq₀ hQ hB₀ hQR hWR hr hb χ κ β (ξ := θ+(r : ℝ))

theorem circleLowTerm_bare_real {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) {Q B₀ R : ℝ} (hQ : 0 < Q) (hB₀ : 0 < B₀)
    (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/B₀ ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β ξ : ℝ) :
    circleLowTerm N hN q₀ Q B₀ χ κ β r (ξ : PrimeCircle)=
      ∑' k : ℤ,rationalLowModelTerm N q₀ Q B₀ χ κ β r (ξ+(k : ℝ)) := by
  rw [circleLowTerm_real]
  apply tsum_congr
  intro k
  rw [centeredLowSymbol_bare hN r hq₀ hQ hB₀ hQR hWR hr hb χ κ β]
  congr 1
  ring

end PrimeSquares
