import PrimeSquares.MajorArcBudgetGeometry

namespace PrimeSquares

/-- Uniform in Q, the finite set of centers, exceptional data and the chosen major arc.
The sole distribution input is the explicit progression-prefix inequality. -/
theorem finiteMajorArcError_uniform_log_rate {C c A : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8)*Real.sqrt (Real.log N) →
    ∀ (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
      (β ξ : ℝ), 0 < β → β ≤ 1 →
    (∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) →
    (∀ r ∈ Γ, (r.den : ℝ) ≤ sourceMajorArcScale N Q) →
    (∀ r ∈ Γ, ‖κ r‖ ≤ 1) →
    ∀ r₀ ∈ Γ,
    |ξ-(r₀ : ℝ)| ≤ sourceMajorArcScale N Q/((r₀.den : ℝ)*(N : ℝ)^2) →
    (∀ u : (ZMod r₀.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r₀.den u t -
        progressionPowerModel r₀.den (κ r₀*χ r₀ u) β t‖ ≤
          (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) →
    ‖finiteMajorArcError Γ N χ κ β ξ‖ ≤
      (2 : ℝ)^A * Q^(-(1/2 : ℝ)) * (1+Real.log N)^(-A) := by
  obtain ⟨N₁, _, hp⟩ := sourceMajorArc_parameter_threshold hc
  obtain ⟨N₂, hN₂, hg⟩ := sourceMajorArc_uniform_geometry hc
  obtain ⟨N₃, hb⟩ := sourceMajorArcScale_uniform_model_log_rate hC hA
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN Q hQ hQlog Γ χ κ β ξ hβ0 hβ1 hΓ hden hκ r₀ hr₀ hξ hprefix
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hn3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hR, hl, hbudget, he⟩ := hp N hn1 Q hQ hQlog
  obtain ⟨hs, hcore⟩ := hg N hn2 Q hQ hQlog
  have hm := finiteMajorArcError_from_prefix (by omega : 2 ≤ N) Γ χ κ hβ0 hβ1
    hR hC hΓ hden hκ hr₀ hs hcore hξ hl hbudget he hprefix
  exact hm.trans (hb N hn3 Q hQ)

end PrimeSquares
