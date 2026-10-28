import PrimeSquares.OrdinaryOnlySourceSymbol
import PrimeSquares.OrdinaryRationalCircleSource
import PrimeSquares.CompactLiftExtensionality

namespace PrimeSquares

theorem circleLowTerm_no_exception {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) (hw : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) (B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleLowTerm N hN q₀ Q B₀ χ (fun _ => 0) β r=
      if (r.den : ℝ) ≤ Q then ordinaryRationalCircleLow N hN Q hQ hw r else 0 := by
  have hc := centeredLowSymbol_no_exception hN r hQ hQR hr hb q₀ B₀ χ β
  change circleFrequencyShift (compactCircleLift (centeredLowSymbol N hN q₀ Q B₀ χ (fun _ => 0) β r)
    (centeredLowSymbol_support N hN q₀ Q B₀ χ (fun _ => 0) β r)) (((r : ℝ) : PrimeCircle))=_
  by_cases hd : (r.den : ℝ) ≤ Q
  · rw [ite_eq_left hd] at hc ⊢
    rw [compactCircleLift_congr _ _ _ (ordinaryCenteredLow_support N hN hQ hw r) hc]
    exact ordinaryCenteredLow_circle N hN hQ hw r
  · rw [ite_eq_right hd] at hc ⊢
    rw [compactCircleLift_congr _ _ _ (fun _ _ => rfl) hc]
    erw [compactCircleLift_zero]
    exact circleFrequencyShift_zero _

end PrimeSquares
