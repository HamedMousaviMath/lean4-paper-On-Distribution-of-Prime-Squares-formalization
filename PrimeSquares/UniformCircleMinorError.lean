import PrimeSquares.UniformComplementaryBudget
import PrimeSquares.CircleModelOperators

open Filter
namespace PrimeSquares

theorem circleModelTailBudget_uniform_log_rate {A : ℝ} (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      circleModelTailBudget (sourceMajorArcScale N Q) ≤
        (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  have he : ∀ᶠ R : ℝ in atTop, circleModelTailBudget R ≤ R^(-(1/6 : ℝ)) := by
    filter_upwards [eventually_circleModelTailBudget,eventually_ge_atTop (1 : ℝ)] with R hR hR1
    exact hR.trans (Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num))
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  obtain ⟨N₁,hN₁⟩ := sourceMajorArcScale_uniform_lower B
  obtain ⟨N₂,hN₂⟩ := sourceMajorArcScale_logarithmic_rate hA
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ
  exact (hB _ (hN₁ N ((le_max_left _ _).trans hN) Q)).trans
    (hN₂ N ((le_max_right _ _).trans hN) Q hQ)

theorem circleMajorArcError_minor_from_inputs {N : ℕ} (hN : 4 ≤ N)
    {C B c R ξ β : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hpow : R^4 ≤ (N : ℝ)/2)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hκ : ∀ r ∈ sourceRationalCenters R, ‖κ r‖ ≤ 1)
    (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) (hout : OutsideSourceMajorArcs N R ξ)
    (hRen : RenBalancedInput N ξ C c) (hGhosh : GhoshBalancedInput N ξ B) :
    ‖circleMajorArcError (sourceRationalCenters R) N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤
      complementaryMinorBudget N C B c R+circleModelTailBudget R := by
  have hs := annularMangoldt_complementary_minor_bound hN hC hB hR hpow hout hRen hGhosh
  have hv := outsideSourceMajorArcs_circleModel_norm (by omega : 2 ≤ N) hR χ κ hβ0 hβ1 hκ hξ hout
  change ‖_ - circleMajorArcModel (sourceRationalCenters R) N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hs hv)

theorem circleMajorArcError_minor_uniform {C B d c A : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ),
      0 ≤ β → β ≤ 1 → ξ ∈ Set.Icc (-1 : ℝ) 2 →
      (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1) →
      OutsideSourceMajorArcs N (sourceMajorArcScale N Q) ξ →
      RenBalancedInput N ξ C d → GhoshBalancedInput N ξ B →
    ∀ hN : 1 ≤ N,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β (ξ : PrimeCircle)‖ ≤
      2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := by
  obtain ⟨N₁,hN₁,hp⟩ := sourceMajorArcScale_uniform_fourth_power hc
  obtain ⟨N₂,_,hb⟩ := complementaryMinorBudget_uniform_log_rate hC hB hd hA
  obtain ⟨N₃,ht⟩ := circleModelTailBudget_uniform_log_rate hA
  refine ⟨max N₁ (max N₂ N₃),by omega,?_⟩
  intro N hN Q hQ hQl χ κ β ξ hβ0 hβ1 hξ hκ hout hRen hGhosh hn
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hn3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hR := sourceMajorArcScale_one_le (N := (N : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N)) Q
  have hm := circleMajorArcError_minor_from_inputs (by omega : 4 ≤ N) hC hB hR
    (hp N hn1 Q hQ hQl) χ κ hβ0 hβ1 hκ hξ hout hRen hGhosh
  have hsum := add_le_add (hb N hn2 Q hQ) (ht N hn3 Q hQ)
  exact hm.trans (by linarith only [hsum])

end PrimeSquares
