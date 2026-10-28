import PrimeSquares.SourceRangeMajorArc
import PrimeSquares.UniformMajorArcBudget

open Filter

namespace PrimeSquares

theorem majorArc_geometry_of_budget {N R : ℝ} (hN : 2 < N) (hR : 1 ≤ R)
    (hlog : 1 ≤ Real.log N) (hbudget : R^5*Real.log N ≤ Real.sqrt N) :
    2*R^3 < N^2 ∧ 2*R^4 ≤ N^2 := by
  have hp5 : R^5 ≤ Real.sqrt N := by
    calc
      R^5 = R^5*1 := (mul_one _).symm
      _ ≤ R^5*Real.log N := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ _ := hbudget
  have hs : Real.sqrt N ≤ N := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hp3 : R^3 ≤ R^5 := pow_le_pow_right₀ hR (by norm_num)
  have hp4 : R^4 ≤ R^5 := pow_le_pow_right₀ hR (by norm_num)
  constructor <;> nlinarith

theorem sourceMajorArc_uniform_geometry {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8)*Real.sqrt (Real.log N) →
      2*(sourceMajorArcScale N Q)^3 < (N : ℝ)^2 ∧
      2*(sourceMajorArcScale N Q)^4 ≤ (N : ℝ)^2 := by
  obtain ⟨N₁, _, hN₁⟩ := sourceMajorArc_parameter_threshold hc
  have ht := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ht
  refine ⟨max (max N₁ N₂) 3, le_max_right _ _, ?_⟩
  intro N hN Q hQ hQlog
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hn3 : 3 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hR, _, hb, _⟩ := hN₁ N hn1 Q hQ hQlog
  exact majorArc_geometry_of_budget (by exact_mod_cast (by omega : 2 < N)) hR (hN₂ N hn2) hb

end PrimeSquares
