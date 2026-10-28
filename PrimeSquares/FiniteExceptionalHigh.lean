import PrimeSquares.CircleExceptionalCollar
open Finset
namespace PrimeSquares
noncomputable def circleExceptionalHighModel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,circleExceptionalHigh N hN q₀ Q B χ κ β r
theorem circleHighModel_ordinary_sub_exceptional (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleHighModel Γ N hN q₀ Q B χ κ β=
      circleHighModel Γ N hN q₀ Q B χ (fun _ => 0) β-circleExceptionalHighModel Γ N hN q₀ Q B χ κ β := by
  unfold circleHighModel circleExceptionalHighModel
  rw [←sum_sub_distrib]
  exact sum_congr rfl (fun r _ => circleHighTerm_ordinary_sub_exceptional N hN q₀ Q B χ κ β r)
end PrimeSquares
