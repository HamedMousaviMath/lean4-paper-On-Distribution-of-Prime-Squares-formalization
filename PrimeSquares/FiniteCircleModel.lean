import PrimeSquares.CircleRationalModelNorm

open Finset
namespace PrimeSquares

noncomputable def circleMajorArcModel (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle, ℂ) :=
  ∑ r ∈ Γ, circleRationalModelTerm N hN χ κ β r

noncomputable def circleMajorArcError (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) : C(PrimeCircle, ℂ) :=
  annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt -
    circleMajorArcModel Γ N hN χ κ β

theorem circleMajorArcModel_real (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ) :
    circleMajorArcModel Γ N hN χ κ β (ξ : PrimeCircle) =
      ∑ r ∈ Γ, ∑' k : ℤ, centeredRationalSymbol N hN χ κ β r (ξ-(r : ℝ)+k) := by
  simp only [circleMajorArcModel, ContinuousMap.sum_apply, circleRationalModelTerm_real]

theorem circleMajorArcModel_norm {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1) (θ : PrimeCircle) :
    ‖circleMajorArcModel Γ N (by omega) χ κ β θ‖ ≤
      ∑ r ∈ Γ, 3*(gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ))) := by
  change ‖(∑ r ∈ Γ, circleRationalModelTerm N (by omega) χ κ β r) θ‖ ≤ _
  rw [ContinuousMap.sum_apply]
  exact (norm_sum_le _ _).trans (sum_le_sum (fun r hr =>
    circleRationalModelTerm_norm hN χ κ hβ0 hβ1 r (hκ r hr) θ))

end PrimeSquares
