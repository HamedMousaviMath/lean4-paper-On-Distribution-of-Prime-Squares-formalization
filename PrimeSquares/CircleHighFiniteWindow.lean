import PrimeSquares.CircleHighWindow
import PrimeSquares.CircleFundamentalBounds

open Finset
namespace PrimeSquares

theorem circleHighModel_finite_window (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    circleHighModel Γ N hN q₀ Q B χ κ β (ξ : PrimeCircle)=
      (∑ r ∈ Γ,centeredHighSymbol N hN q₀ Q B χ κ β r (ξ-1-(r : ℝ)))+
      (∑ r ∈ Γ,centeredHighSymbol N hN q₀ Q B χ κ β r (ξ-(r : ℝ)))+
      (∑ r ∈ Γ,centeredHighSymbol N hN q₀ Q B χ κ β r (ξ+1-(r : ℝ))) := by
  classical
  simp only [circleHighModel,ContinuousMap.sum_apply]
  calc
    _ = ∑ r ∈ Γ,(centeredHighSymbol N hN q₀ Q B χ κ β r (ξ-1-(r : ℝ))+
        centeredHighSymbol N hN q₀ Q B χ κ β r (ξ-(r : ℝ))+
        centeredHighSymbol N hN q₀ Q B χ κ β r (ξ+1-(r : ℝ))) := by
      apply sum_congr rfl
      intro r hr
      rw [circleHighTerm_unit_window N hN q₀ Q B χ κ β r (hΓ r hr) hξ]
      have h1 : ξ-(r : ℝ)-1=ξ-1-(r : ℝ) := by ring
      have h3 : ξ-(r : ℝ)+1=ξ+1-(r : ℝ) := by ring
      simp only [compactPeriodWindow,h1,h3]
    _ = _ := by rw [sum_add_distrib,sum_add_distrib]

end PrimeSquares
