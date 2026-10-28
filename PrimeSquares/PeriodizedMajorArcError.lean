import PrimeSquares.PeriodizedModelTails
import PrimeSquares.MajorArcBudgetGeometry

open Finset
namespace PrimeSquares

theorem majorArc_representative_range {N R ξ : ℝ} {r : ℚ}
    (hN : 0 < N) (hR : 1 ≤ R) (hsep : 2*R^3 < N^2)
    (hr : r ∈ Set.Ico (0 : ℚ) 1)
    (hξ : |ξ-(r : ℝ)| ≤ R/((r.den : ℝ)*N^2)) :
    ξ ∈ Set.Icc (-1 : ℝ) 2 := by
  have hrd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hRp : 0 < R := by linarith
  have hpow : R ≤ R^3 := le_self_pow₀ hR (by decide)
  have hdn : R ≤ (r.den : ℝ)*N^2 := by nlinarith [sq_nonneg N]
  have hw : R/((r.den : ℝ)*N^2) ≤ 1 :=
    (div_le_one (mul_pos (by linarith) (sq_pos_of_pos hN))).mpr hdn
  have hlr : (0 : ℝ) ≤ r := by exact_mod_cast hr.1
  have hur : (r : ℝ) < 1 := by exact_mod_cast hr.2
  obtain ⟨hl,hu⟩ := abs_le.mp (hξ.trans hw)
  exact ⟨by linarith,by linarith⟩

theorem realModelTailBudget_nonneg {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ realModelTailBudget R := by
  have hl := Real.log_nonneg hR
  have hG := gaussModelConstant_pos
  dsimp [realModelTailBudget]
  positivity

theorem circleMajorArcError_from_prefix {N : ℕ} (hN : 2 ≤ N)
    (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {R ξ C c : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1)
    {r₀ : ℚ} (hr₀ : r₀ ∈ Γ)
    (hsep : 2*R^3 < (N : ℝ)^2) (hcore : 2*R^4 ≤ (N : ℝ)^2)
    (hξ : |ξ-(r₀ : ℝ)| ≤ R/((r₀.den : ℝ)*(N : ℝ)^2))
    (hlog : Real.log R ≤ Real.log N) (hbudget : R^5*Real.log N ≤ Real.sqrt N)
    (hexp : 7*Real.log R ≤ c*Real.sqrt (Real.log N))
    (hprefix : ∀ u : (ZMod r₀.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r₀.den u t -
        progressionPowerModel r₀.den (κ r₀ * χ r₀ u) β t‖ ≤
        (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) :
    ‖circleMajorArcError Γ N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤ circleApproxBudget C R := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  have hξrange := majorArc_representative_range hNp hR hsep (hΓ r₀ hr₀) hξ
  have hzero : (0 : ℤ) ∈ fivePeriodShifts := by decide
  have hsum : finiteMajorArcModel Γ N χ κ β ξ +
      (∑ k ∈ fivePeriodShifts.erase 0, finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))) =
      circleMajorArcModel Γ N (by omega) χ κ β (ξ : PrimeCircle) := by
    rw [circleMajorArcModel_five Γ N (by omega) χ κ β hΓ hξrange]
    simpa only [Int.cast_zero,add_zero] using
      add_sum_erase fivePeriodShifts (fun k : ℤ => finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))) hzero
  have htail : ‖∑ k ∈ fivePeriodShifts.erase 0,
      finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))‖ ≤ 4*realModelTailBudget R := by
    calc
      _ ≤ ∑ k ∈ fivePeriodShifts.erase 0, ‖finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ ∈ fivePeriodShifts.erase 0, realModelTailBudget R := by
        apply sum_le_sum
        intro k hk
        have hkn : k ≠ 0 := (mem_erase.mp hk).1
        exact finiteMajorArcModel_outside_norm hN Γ χ κ hβ0.le hβ1 hR hΓ hden hκ
          (fun r hr => (canonicalLift_other_outside hNp hR hsep (hΓ r₀ hr₀) (hΓ r hr)
            (hden r₀ hr₀) (hden r hr) hξ (Or.inr hkn)).le)
      _ = _ := by
        have hc : (fivePeriodShifts.erase 0).card = 4 := by decide
        simp only [sum_const,nsmul_eq_mul,hc,Nat.cast_ofNat]
  have hm := finiteMajorArcError_from_prefix hN Γ χ κ hβ0 hβ1 hR hC hΓ hden hκ hr₀
    hsep hcore hξ hlog hbudget hexp hprefix
  have he : circleMajorArcError Γ N (by omega) χ κ β (ξ : PrimeCircle) =
      finiteMajorArcError Γ N χ κ β ξ -
        ∑ k ∈ fivePeriodShifts.erase 0, finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ)) := by
    change _ - circleMajorArcModel Γ N (by omega) χ κ β (ξ : PrimeCircle) = _
    rw [←hsum,finiteMajorArcError]
    ring
  have hG : 0 ≤ gaussModelConstant*R^(-(5/12 : ℝ)) := by
    have hg := gaussModelConstant_pos
    positivity
  rw [he]
  calc
    _ ≤ ‖finiteMajorArcError Γ N χ κ β ξ‖ +
        ‖∑ k ∈ fivePeriodShifts.erase 0, finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))‖ := norm_sub_le _ _
    _ ≤ (4+(2+4*Real.pi)*C)/R^5 + realModelTailBudget R + 4*realModelTailBudget R :=
      add_le_add hm htail
    _ ≤ circleApproxBudget C R := by dsimp [circleApproxBudget,circleModelTailBudget];linarith

theorem circleMajorArcError_uniform_log_rate {C c A : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ : ℝ),
    0 < β → β ≤ 1 →
    (∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q), ‖κ r‖ ≤ 1) →
    ∀ r₀ ∈ sourceRationalCenters (sourceMajorArcScale N Q),
    |ξ-(r₀ : ℝ)| ≤ sourceMajorArcScale N Q/((r₀.den : ℝ)*(N : ℝ)^2) →
    (∀ u : (ZMod r₀.den)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix r₀.den u t -
        progressionPowerModel r₀.den (κ r₀*χ r₀ u) β t‖ ≤
          (N : ℝ)*(C*Real.exp (-c*Real.sqrt (Real.log N)))) →
    ∀ hN : 1 ≤ N,
    ‖circleMajorArcError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN χ κ β
      (ξ : PrimeCircle)‖ ≤ (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨N₁,_,hp⟩ := sourceMajorArc_parameter_threshold hc
  obtain ⟨N₂,hN₂,hg⟩ := sourceMajorArc_uniform_geometry hc
  obtain ⟨N₃,hb⟩ := circleApproxBudget_uniform_log_rate hC hA
  refine ⟨max N₁ (max N₂ N₃),by omega,?_⟩
  intro N hN Q hQ hQlog χ κ β ξ hβ0 hβ1 hκ r₀ hr₀ hξ hprefix hn
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hn3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hR,hl,hbudget,he⟩ := hp N hn1 Q hQ hQlog
  obtain ⟨hs,hcore⟩ := hg N hn2 Q hQ hQlog
  have hindex := fun r hr => (mem_sourceRationalCenters (by linarith : 0 ≤ sourceMajorArcScale N Q) r).mp hr
  exact (circleMajorArcError_from_prefix (by omega : 2 ≤ N) _ χ κ hβ0 hβ1 hR hC
    (fun r hr => (hindex r hr).1) (fun r hr => (hindex r hr).2) hκ hr₀
    hs hcore hξ hl hbudget he hprefix).trans (hb N hn3 Q hQ)

end PrimeSquares
