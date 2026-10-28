import PrimeSquares.LargeOrdinaryCenteredHigh

namespace PrimeSquares

theorem circleLowTerm_large_ordinary_zero (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (r : ℚ) (hr : Q < (r.den : ℝ)) :
    circleLowTerm N hN q₀ Q B χ (fun _ => 0) β r=0 := by
  ext θ
  change compactPeriodWindow (centeredLowSymbol N hN q₀ Q B χ (fun _ => 0) β r) _=0
  rw [centeredLowSymbol_large_ordinary_zero N hN q₀ Q B χ β r hr]
  simp only [compactPeriodWindow,ContinuousMap.zero_apply,zero_add]

theorem circleHighTerm_large_ordinary (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (r : ℚ) (hr : Q < (r.den : ℝ)) :
    circleHighTerm N hN q₀ Q B χ (fun _ => 0) β r=circleRationalModelTerm N hN χ (fun _ => 0) β r := by
  have hh := circleTerm_low_add_high N hN q₀ Q B χ (fun _ => 0) β r
  rw [circleLowTerm_large_ordinary_zero N hN q₀ Q B χ β r hr,zero_add] at hh
  exact hh

end PrimeSquares
