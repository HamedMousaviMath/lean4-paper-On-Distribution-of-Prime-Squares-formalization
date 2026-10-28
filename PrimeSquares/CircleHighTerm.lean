import PrimeSquares.CircleLowTerm

namespace PrimeSquares

noncomputable def circleHighTerm (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(PrimeCircle, ℂ) :=
  (compactCircleLift (centeredHighSymbol N hN q₀ Q B₀ χ κ β r)
    (centeredHighSymbol_support N hN q₀ Q B₀ χ κ β r)).comp
      ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩

theorem circleTerm_low_add_high (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    circleLowTerm N hN q₀ Q B₀ χ κ β r + circleHighTerm N hN q₀ Q B₀ χ κ β r =
      circleRationalModelTerm N hN χ κ β r := by
  ext θ
  change compactPeriodWindow (centeredLowSymbol N hN q₀ Q B₀ χ κ β r) _ +
      compactPeriodWindow (centeredHighSymbol N hN q₀ Q B₀ χ κ β r) _ =
      compactPeriodWindow (centeredRationalSymbol N hN χ κ β r) _
  simp only [compactPeriodWindow,centeredHighSymbol,ContinuousMap.sub_apply]
  ring

theorem circleHighTerm_real (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    circleHighTerm N hN q₀ Q B₀ χ κ β r (ξ : PrimeCircle) =
      ∑' k : ℤ, centeredHighSymbol N hN q₀ Q B₀ χ κ β r (ξ-(r : ℝ)+k) := by
  change compactCircleLift (centeredHighSymbol N hN q₀ Q B₀ χ κ β r)
    (centeredHighSymbol_support N hN q₀ Q B₀ χ κ β r)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [← AddCircle.coe_sub]
  exact compactCircleLift_all_real _ _ _

end PrimeSquares
