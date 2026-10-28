import PrimeSquares.DyadicCircleErrorBudget
import PrimeSquares.OperatorDecaySeries

open scoped lp
namespace PrimeSquares

theorem dyadicCircleError_norm_series {P C B d c s : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hs : 2 ≤ s) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ J : ℕ, N₀ ≤ (2 : ℕ)^J → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log (((2 : ℕ)^J : ℕ) : ℝ)) →
    ∀ (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ),
      (∀ j : ℕ, J ≤ j → CircleAnalyticInputs (2^j) Q (χ j) (κ j) (β j) P C B d c) →
      Summable (fun j : ℕ => ‖dyadicCircleErrorOperator Q χ κ β (J+j)‖) ∧
      (∑' j : ℕ, ‖dyadicCircleErrorOperator Q χ κ β (J+j)‖) ≤
        2*(dyadicErrorConstant s*Q^(-(1/2 : ℝ)))*((J : ℝ)+1)^(1-s) := by
  obtain ⟨N₀,hN₀,h⟩ := dyadicCircleError_operator_decay hP hC hB hd hc (by linarith : 0 ≤ s)
  refine ⟨N₀,hN₀,?_⟩
  intro J hJ Q hQ hQl χ κ β hi
  have hK : 0 ≤ dyadicErrorConstant s*Q^(-(1/2 : ℝ)) := by
    have hk := dyadicErrorConstant_pos s
    positivity
  have ht : ∀ j : ℕ, ‖dyadicCircleErrorOperator Q χ κ β (J+j)‖ ≤
      (dyadicErrorConstant s*Q^(-(1/2 : ℝ)))*((J+j : ℕ)+1 : ℝ)^(-s) := by
    intro j
    exact h J hJ Q hQ hQl χ κ β hi (J+j) (by omega)
  exact ⟨operator_norm_shift_summable hK hs J _ ht,operator_norm_shift_tsum_bound hK hs J _ ht⟩

end PrimeSquares
