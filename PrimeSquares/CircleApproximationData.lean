import PrimeSquares.GlobalCircleApproximation
import PrimeSquares.CircleFundamentalBounds

open scoped lp
namespace PrimeSquares

structure CircleAnalyticInputs (N : ℕ) (Q : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β P C B d c : ℝ) : Prop where
  beta_pos : 0 < β
  beta_le_one : β ≤ 1
  coefficient_bound : ∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1
  progression_prefix : ∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q),
    ∀ u : (ZMod r.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
    ‖progressionMangoldtPrefix r.den u t-progressionPowerModel r.den (κ r*χ r u) β t‖ ≤
      (N : ℝ)*(P*Real.exp (-c*Real.sqrt (Real.log N)))
  ren_input : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, RenBalancedInput N ξ C d
  ghosh_input : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, GhoshBalancedInput N ξ B

theorem globalCircleApproximation_all_points {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      CircleAnalyticInputs N Q χ κ β P C B d c → ∀ hN : 1 ≤ N, ∀ θ : PrimeCircle,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β θ‖ ≤
      2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := by
  obtain ⟨N₀,hN₀,h⟩ := globalCircleApproximation_uniform hP hC hB hd hc hA
  refine ⟨N₀,hN₀,?_⟩
  intro N hn Q hQ hQl χ κ β hi hN
  apply circleBound_from_fundamental_interval
  intro ξ hξ
  exact h N hn Q hQ hQl χ κ β hi.beta_pos hi.beta_le_one hi.coefficient_bound
    hi.progression_prefix ξ hξ (hi.ren_input ξ hξ) (hi.ghosh_input ξ hξ) hN

theorem globalCircleApproximation_l2_operator {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      CircleAnalyticInputs N Q χ κ β P C B d c → ∀ hN : 1 ≤ N,
    ‖circleMajorArcErrorOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β‖ ≤
      2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := by
  obtain ⟨N₀,hN₀,h⟩ := globalCircleApproximation_all_points hP hC hB hd hc hA
  refine ⟨N₀,hN₀,?_⟩
  intro N hn Q hQ hQl χ κ β hi hN
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact circleModel_error_operator_bound _ N hN χ κ β (by positivity)
    (h N hn Q hQ hQl χ κ β hi hN)

end PrimeSquares
