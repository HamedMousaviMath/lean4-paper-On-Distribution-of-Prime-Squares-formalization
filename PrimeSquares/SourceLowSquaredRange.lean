import PrimeSquares.SourceLowRangeBudget

namespace PrimeSquares

theorem sourceFullLow_squared_level {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hqR : (q₀ : ℝ) ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2) :
    circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β=
      realCombinedLowModel N hN q₀ χ₀ Q (by linarith) (source_squared_low_width hQ hQR hb) β ⌊R⌋₊ active := by
  have hR : 1 ≤ R := hQ.trans hQR
  have hR2 := radius_le_square hR
  have hgeo : 2*(R^2)^4 ≤ (N : ℝ)^2 := by convert hb using 1;ring
  exact truncatedSourceLow_identity hN q₀ χ₀ active β ⌊R⌋₊ hQ (hQR.trans hR2)
    (source_exceptional_squared_radius (NeZero.pos q₀) (by linarith) hQR hqR)
    ((Nat.floor_le (by linarith : 0 ≤ R)).trans hR2) (Nat.floor_mono hQR) hgeo

end PrimeSquares
