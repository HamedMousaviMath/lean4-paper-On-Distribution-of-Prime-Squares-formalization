import PrimeSquares.PeriodizedMajorArcError

open Finset
namespace PrimeSquares

theorem annularMangoldt_intermediate_norm {N : ℕ} (hN : 2 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {R ξ C c : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (r : ℚ) (hκ : ‖κ r‖ ≤ 1)
    (hql : R < (r.den : ℝ)) (hqu : (r.den : ℝ) ≤ R^(11/10 : ℝ))
    (hξ : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*(N : ℝ)^2))
    (hlog : Real.log R ≤ Real.log N) (hbudget : R^5*Real.log N ≤ Real.sqrt N)
    (hexp : 7*Real.log R ≤ c*Real.sqrt (Real.log N))
    (hprefix : ∀ u : (ZMod r.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r.den u t -
        progressionPowerModel r.den (κ r*χ r u) β t‖ ≤
        (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      (4+(2+4*Real.pi)*C)/R^5 + gaussModelConstant*R^(-(5/12 : ℝ)) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  have hg := ((Classical.choose_spec annularGaussModel_uniform_bounds).2
    N r.den (χ r) (κ r) β (r.num : ZMod r.den) hN hβ0.le hβ1 ha hκ).1 (ξ-(r : ℝ))
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R) hql.le (by norm_num : -(5/12 : ℝ) ≤ 0)
  have hgauss : ‖annularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (ξ-(r : ℝ))‖ ≤
      gaussModelConstant*R^(-(5/12 : ℝ)) :=
    hg.trans (mul_le_mul_of_nonneg_left hp gaussModelConstant_pos.le)
  have hs := annularMangoldt_majorArc_inverse_fifth (by omega : 1 ≤ N)
    (χ r) (κ r) hβ0 r.num (ξ-(r : ℝ)) hR hC hqu hξ hlog hbudget hexp hprefix
  rw [rationalCenter_add_offset] at hs
  change ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
    annularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (ξ-(r : ℝ))‖ ≤ _ at hs
  calc
    _ = ‖(annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
        annularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (ξ-(r : ℝ))) +
        annularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (ξ-(r : ℝ))‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hs hgauss)

theorem circleMajorArcError_intermediate_from_prefix {N : ℕ} (hN : 2 ≤ N)
    (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {R ξ C c : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1)
    (hξrange : ξ ∈ Set.Icc (-1 : ℝ) 2)
    (hout : ∀ r ∈ Γ, ∀ k ∈ fivePeriodShifts,
      R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ+(k : ℝ)-(r : ℝ)|)
    (r : ℚ) (hκr : ‖κ r‖ ≤ 1)
    (hql : R < (r.den : ℝ)) (hqu : (r.den : ℝ) ≤ R^(11/10 : ℝ))
    (hξ : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*(N : ℝ)^2))
    (hlog : Real.log R ≤ Real.log N) (hbudget : R^5*Real.log N ≤ Real.sqrt N)
    (hexp : 7*Real.log R ≤ c*Real.sqrt (Real.log N))
    (hprefix : ∀ u : (ZMod r.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r.den u t -
        progressionPowerModel r.den (κ r*χ r u) β t‖ ≤
        (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) :
    ‖circleMajorArcError Γ N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤ circleApproxBudget C R := by
  have hs := annularMangoldt_intermediate_norm hN χ κ hβ0 hβ1 hR hC r hκr hql hqu hξ hlog hbudget hexp hprefix
  have hv := circleMajorArcModel_outside_norm hN Γ χ κ hβ0.le hβ1 hR hΓ hden hκ hξrange hout
  change ‖_ - circleMajorArcModel Γ N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hs hv)

theorem circleMajorArcError_intermediate_uniform_log_rate {C c A : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ),
    0 < β → β ≤ 1 → ξ ∈ Set.Icc (-1 : ℝ) 2 →
    (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1) →
    (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ∀ k ∈ fivePeriodShifts,
      sourceMajorArcScale N Q/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ+(k : ℝ)-(r : ℝ)|) →
    ∀ r : ℚ, ‖κ r‖ ≤ 1 →
    sourceMajorArcScale N Q < (r.den : ℝ) →
    (r.den : ℝ) ≤ (sourceMajorArcScale N Q)^(11/10 : ℝ) →
    |ξ-(r : ℝ)| ≤ sourceMajorArcScale N Q/((r.den : ℝ)*(N : ℝ)^2) →
    (∀ u : (ZMod r.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r.den u t -
        progressionPowerModel r.den (κ r*χ r u) β t‖ ≤
          (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) →
    ∀ hN : 1 ≤ N,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β
      (ξ : PrimeCircle)‖ ≤ (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨N₁,_,hp⟩ := sourceMajorArc_parameter_threshold hc
  obtain ⟨N₂,hb⟩ := circleApproxBudget_uniform_log_rate hC hA
  refine ⟨max 2 (max N₁ N₂),by omega,?_⟩
  intro N hN Q hQ hQlog χ κ β ξ hβ0 hβ1 hξrange hκ hout r hκr hql hqu hξ hprefix hn
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hR,hl,hbudget,he⟩ := hp N hn1 Q hQ hQlog
  have hindex := fun s hs => (mem_sourceRationalCenters (by linarith : 0 ≤ sourceMajorArcScale N Q) s).mp hs
  exact (circleMajorArcError_intermediate_from_prefix (by omega : 2 ≤ N) _ χ κ hβ0 hβ1 hR hC
    (fun s hs => (hindex s hs).1) (fun s hs => (hindex s hs).2) hκ hξrange hout r hκr
    hql hqu hξ hl hbudget he hprefix).trans (hb N hn2 Q hQ)

end PrimeSquares
