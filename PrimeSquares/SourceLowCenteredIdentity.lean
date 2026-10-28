import PrimeSquares.ExceptionalRationalCircle
import PrimeSquares.OrdinaryRationalCircleSource
import PrimeSquares.SourceLowCircleRealFormula

namespace PrimeSquares

theorem sourceCenteredLow_identity {N : ℕ} (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (active : Bool) (β : ℝ) (r : ℚ) {Q R : ℝ}
    (hQ : 0 < Q) (hQR : Q ≤ R) (hWR : Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ R)
    (hr : (r.den : ℝ) ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) :
    centeredLowSymbol N hN q₀ Q (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀)
      (sourceExceptionalSelector q₀ active) β r=
      (if (r.den : ℝ) ≤ Q then ordinaryCenteredLow N hN Q r else 0)-
      (if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
        then exceptionalCenteredLow N hN q₀ χ₀ Q β r else 0) := by
  ext θ
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  rw [centeredLowSymbol_bare hN r (NeZero.pos q₀) hQ hB hQR hWR hr hb]
  unfold rationalLowModelTerm
  rw [←ordinaryCenteredLow_source N hN Q r θ,
    exceptionalCenteredLow_source N hN (NeZero.pos q₀) χ₀ Q β active r θ]
  split_ifs <;> simp_all [sub_eq_add_neg]

end PrimeSquares
