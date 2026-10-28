import PrimeSquares.UniformCircleMinorError
import PrimeSquares.WrappedCircleMajorUniform

namespace PrimeSquares

theorem globalCircleApproximation_uniform {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      0 < β → β ≤ 1 →
      (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1) →
      (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ∀ u : (ZMod r.den)ˣ,
        ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
        ‖progressionMangoldtPrefix r.den u t-progressionPowerModel r.den (κ r*χ r u) β t‖ ≤
          (N : ℝ)*(P*Real.exp (-c*Real.sqrt (Real.log N)))) →
    ∀ ξ ∈ Set.Icc (0 : ℝ) 1, RenBalancedInput N ξ C d → GhoshBalancedInput N ξ B →
    ∀ hN : 1 ≤ N,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β (ξ : PrimeCircle)‖ ≤
      2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := by
  obtain ⟨N₁,_,hm⟩ := circleMajorArcError_major_lift_uniform hP hc hA
  obtain ⟨N₂,hN₂,hn⟩ := circleMajorArcError_minor_uniform hC hB hd hc hA
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN Q hQ hQl χ κ β hβ0 hβ1 hκ hprefix ξ hξ hRen hGhosh hNpos
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans hN
  by_cases harc : ∃ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ∃ k : ℤ,
      |ξ+(k : ℝ)-(r : ℝ)| ≤ sourceMajorArcScale N Q/((r.den : ℝ)*(N : ℝ)^2)
  · obtain ⟨r,hr,k,hkr⟩ := harc
    have h := hm N hn1 Q hQ hQl χ κ β ξ hβ0 hβ1 hκ r hr k hkr (hprefix r hr) hNpos
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
    have hnonneg : 0 ≤ (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by positivity
    exact h.trans (by linarith)
  · have hout : OutsideSourceMajorArcs N (sourceMajorArcScale N Q) ξ := by
      intro r hr k
      by_contra h
      exact harc ⟨r,hr,k,(lt_of_not_ge h).le⟩
    exact hn N hn2 Q hQ hQl χ κ β ξ hβ0.le hβ1
      ⟨by linarith [hξ.1],by linarith [hξ.2]⟩ hκ hout hRen hGhosh hNpos

end PrimeSquares
