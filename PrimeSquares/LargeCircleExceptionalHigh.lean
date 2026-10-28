import PrimeSquares.LargeCenteredExceptionalHigh
namespace PrimeSquares
theorem circleExceptionalHigh_large (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hr : Q*(q₀ : ℝ)/B < (r.den : ℝ)) :
    circleExceptionalHigh N hN q₀ Q B χ κ β r=
      circleRationalModelTerm N hN χ (fun _ => 0) β r-circleRationalModelTerm N hN χ κ β r := by
  ext θ
  change compactPeriodWindow (centeredExceptionalHigh N hN q₀ Q B χ κ β r) _=
    compactPeriodWindow (centeredRationalSymbol N hN χ (fun _ => 0) β r) _-
    compactPeriodWindow (centeredRationalSymbol N hN χ κ β r) _
  rw [centeredExceptionalHigh_large N hN hq₀ hQ hB χ κ β r hr]
  simp only [compactPeriodWindow,ContinuousMap.sub_apply]
  ring
end PrimeSquares
