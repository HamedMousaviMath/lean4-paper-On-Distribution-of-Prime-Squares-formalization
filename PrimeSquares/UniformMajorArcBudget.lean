import PrimeSquares.MajorArcModelError

open Filter
open scoped Topology

namespace PrimeSquares

noncomputable def finiteMajorArcBudget (C R : ℝ) : ℝ :=
  (4+(2+4*Real.pi)*C)/R^5 +
    (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ))

/-- A single arithmetic threshold controls every Q, rather than one threshold per Q. -/
theorem sourceMajorArcScale_uniform_lower (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, B ≤ sourceMajorArcScale N Q := by
  have ht := Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp Real.tendsto_log_atTop)
  have hn := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (ht.eventually (eventually_ge_atTop B))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hn
  exact ⟨N₀, fun N hN Q => (hN₀ N hN).trans (le_max_left _ _)⟩

theorem sourceMajorArcScale_uniform_model_budget {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ,
      finiteMajorArcBudget C (sourceMajorArcScale N Q) ≤
        (sourceMajorArcScale N Q)^(-(1/6 : ℝ)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_finiteMajorArcBudget hC)
  obtain ⟨N₀, hN₀⟩ := sourceMajorArcScale_uniform_lower B
  exact ⟨N₀, fun N hN Q => hB _ (hN₀ N hN Q)⟩

theorem sourceMajorArcScale_uniform_model_log_rate {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      finiteMajorArcBudget C (sourceMajorArcScale N Q) ≤
        (2 : ℝ)^A * Q^(-(1/2 : ℝ)) * (1+Real.log N)^(-A) := by
  obtain ⟨N₁, hN₁⟩ := sourceMajorArcScale_uniform_model_budget hC
  obtain ⟨N₂, hN₂⟩ := sourceMajorArcScale_logarithmic_rate hA
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN Q hQ
  exact (hN₁ N ((le_max_left _ _).trans hN) Q).trans
    (hN₂ N ((le_max_right _ _).trans hN) Q hQ)

end PrimeSquares
