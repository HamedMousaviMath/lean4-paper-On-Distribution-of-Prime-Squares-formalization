import PrimeSquares.DyadicErrorNormSeries
import PrimeSquares.OperatorMaximalNorm

open scoped lp
namespace PrimeSquares

theorem dyadicCircleError_maximal_power {P C B d c s : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hs : 2 ≤ s) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ J : ℕ, N₀ ≤ (2 : ℕ)^J → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log (((2 : ℕ)^J : ℕ) : ℝ)) →
    ∀ (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ),
      (∀ j : ℕ, J ≤ j → CircleAnalyticInputs (2^j) Q (χ j) (κ j) (β j) P C B d c) →
    ∀ f : ℓ²(ℤ, ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, g x = ⨆ j : ℕ, ‖dyadicCircleErrorOperator Q χ κ β (J+j) f x‖) ∧
      ‖g‖ ≤ 2*(dyadicErrorConstant s*Q^(-(1/2 : ℝ)))*((J : ℝ)+1)^(1-s)*‖f‖ := by
  obtain ⟨N₀,hN₀,h⟩ := dyadicCircleError_norm_series hP hC hB hd hc hs
  refine ⟨N₀,hN₀,?_⟩
  intro J hJ Q hQ hQl χ κ β hi f
  obtain ⟨hseries,hbound⟩ := h J hJ Q hQ hQl χ κ β hi
  refine ⟨operatorMaximalL2 (fun j => dyadicCircleErrorOperator Q χ κ β (J+j)) hseries f,
    fun x => rfl,?_⟩
  exact (operatorMaximalL2_norm_bound _ hseries f).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg f))

end PrimeSquares
