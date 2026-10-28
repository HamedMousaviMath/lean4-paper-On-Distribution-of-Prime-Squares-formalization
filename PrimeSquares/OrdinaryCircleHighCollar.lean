import PrimeSquares.OrdinaryCenteredHighCollar
import PrimeSquares.FiniteCircleHighLow

namespace PrimeSquares

theorem circleHighTerm_ordinary_collar (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (β : ℝ) (r : ℚ) (hr : (r.den : ℝ) ≤ Q) :
    circleHighTerm N hN q₀ Q B χ (fun _ => 0) β r=
      rationalPrincipalGauss r • circleAnnularCollar N hN 1 (r.den : ℝ) Q (Nat.log2 r.den) (r : ℝ) := by
  ext θ
  change compactPeriodWindow (centeredHighSymbol N hN q₀ Q B χ (fun _ => 0) β r) _=
    rationalPrincipalGauss r*compactPeriodWindow (annularCollarSymbol N hN 1 (r.den : ℝ) Q (Nat.log2 r.den)) _
  rw [centeredHighSymbol_ordinary_collar N hN q₀ hq₀ hQ hB χ β r hr]
  simp only [compactPeriodWindow,ContinuousMap.smul_apply,smul_eq_mul]
  ring

end PrimeSquares
