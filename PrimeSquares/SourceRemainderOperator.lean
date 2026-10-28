import PrimeSquares.HighFiniteIndicatorPairing

open scoped lp
namespace PrimeSquares

noncomputable def sourceRemainderOperator (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  circleHighOperator Γ N hN q₀ Q B χ κ β+circleMajorArcErrorOperator Γ N hN χ κ β

theorem annularKernel_low_remainder (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x=
      circleLowOperator Γ N hN q₀ Q B χ κ β (finiteInputLp F f 1) x+
      sourceRemainderOperator Γ N hN q₀ Q B χ κ β (finiteInputLp F f 2) x := by
  rw [annularKernel_finite_low_high_error Γ N hN q₀ Q B χ κ β]
  simp only [sourceRemainderOperator,_root_.add_apply,lp.coeFn_add,Pi.add_apply,add_assoc]

theorem sourceRemainderOperator_norm (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) {b e : ℝ}
    (hh : ‖circleHighOperator Γ N hN q₀ Q B χ κ β‖ ≤ b)
    (he : ‖circleMajorArcErrorOperator Γ N hN χ κ β‖ ≤ e) :
    ‖sourceRemainderOperator Γ N hN q₀ Q B χ κ β‖ ≤ b+e :=
  (norm_add_le _ _).trans (add_le_add hh he)

end PrimeSquares
