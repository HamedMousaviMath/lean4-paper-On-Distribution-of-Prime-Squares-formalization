import PrimeSquares.DyadicSourceLogBudget

namespace PrimeSquares

theorem sourceRadius_uniform_dyadic_fourth {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ,4 ≤ M₀ ∧ ∀ M : ℕ,M₀ ≤ M → ∀ Q : ℝ,1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log M) → ∀ j : ℕ,
      (sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)^4 ≤ ((((2 : ℕ)^j*M : ℕ) : ℝ))/2 := by
  obtain ⟨M₀,hM₀,hh⟩ := sourceMajorArcScale_uniform_fourth_power hc
  refine ⟨M₀,hM₀,?_⟩
  intro M hm Q hQ hlog j
  have hM : 2 ≤ M := by omega
  have hMN : M ≤ (2 : ℕ)^j*M := by
    have hp : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right M hp
  exact hh _ (hm.trans hMN) Q hQ (source_log_budget_dyadic hc hM hlog j)

end PrimeSquares
