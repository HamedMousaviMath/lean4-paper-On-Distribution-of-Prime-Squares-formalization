import PrimeSquares.CenteredExceptionalCollar
namespace PrimeSquares
noncomputable def circleExceptionalHigh (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (centeredExceptionalHigh N hN q₀ Q B χ κ β r)
    (centeredExceptionalHigh_support N hN q₀ Q B χ κ β r)).comp
      ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩
theorem circleHighTerm_ordinary_sub_exceptional (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    circleHighTerm N hN q₀ Q B χ κ β r=
      circleHighTerm N hN q₀ Q B χ (fun _ => 0) β r-circleExceptionalHigh N hN q₀ Q B χ κ β r := by
  ext θ
  change compactPeriodWindow (centeredHighSymbol N hN q₀ Q B χ κ β r) _=
    compactPeriodWindow (centeredHighSymbol N hN q₀ Q B χ (fun _ => 0) β r) _-
    compactPeriodWindow (centeredExceptionalHigh N hN q₀ Q B χ κ β r) _
  simp only [compactPeriodWindow,centeredExceptionalHigh,ContinuousMap.sub_apply]
  ring
end PrimeSquares
