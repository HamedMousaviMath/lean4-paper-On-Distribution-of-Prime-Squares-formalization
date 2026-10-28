import PrimeSquares.PeriodizedMajorArcError

namespace PrimeSquares

theorem circleMajorArcError_integer_shift (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ) (k : ℤ) :
    circleMajorArcError Γ N hN χ κ β ((ξ+(k : ℝ) : ℝ) : PrimeCircle) =
      circleMajorArcError Γ N hN χ κ β (ξ : PrimeCircle) := by
  rw [primeCircle_coe_integer_shift]

theorem circleMajorArcError_major_lift_uniform {C c A : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ),
      0 < β → β ≤ 1 →
      (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1) →
    ∀ r₀ ∈ sourceRationalCenters (sourceMajorArcScale N Q), ∀ k : ℤ,
      |ξ+(k : ℝ)-(r₀ : ℝ)| ≤ sourceMajorArcScale N Q/((r₀.den : ℝ)*(N : ℝ)^2) →
      (∀ u : (ZMod r₀.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
        ‖progressionMangoldtPrefix r₀.den u t-progressionPowerModel r₀.den (κ r₀*χ r₀ u) β t‖ ≤
          (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) →
    ∀ hN : 1 ≤ N,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β (ξ : PrimeCircle)‖ ≤
      (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨N₀,hN₀,h⟩ := circleMajorArcError_uniform_log_rate hC hc hA
  refine ⟨N₀,hN₀,?_⟩
  intro N hn Q hQ hQl χ κ β ξ hβ0 hβ1 hκ r₀ hr₀ k hξ hprefix hN
  have hm := h N hn Q hQ hQl χ κ β (ξ+(k : ℝ)) hβ0 hβ1 hκ r₀ hr₀ hξ hprefix hN
  rwa [circleMajorArcError_integer_shift] at hm

end PrimeSquares
