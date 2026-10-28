import PrimeSquares.DyadicSourceFourthPower

namespace PrimeSquares

theorem sourceRadius_uniform_dyadic_eighth {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ,4 ≤ M₀ ∧ ∀ M : ℕ,M₀ ≤ M → ∀ Q : ℝ,1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log M) → ∀ j : ℕ,
      2*(sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)^8 ≤ ((((2 : ℕ)^j*M : ℕ) : ℝ))^2 := by
  obtain ⟨M₀,hM₀,hh⟩ := sourceRadius_uniform_dyadic_fourth hc
  refine ⟨M₀,hM₀,?_⟩
  intro M hm Q hQ hlog j
  exact source_fourth_budget_to_eighth (hh M hm Q hQ hlog j)

end PrimeSquares
