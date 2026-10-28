import PrimeSquares.WrappedRationalArcGeometry
import PrimeSquares.FiniteCircleModel
import PrimeSquares.SourceModelLogarithmicRate
import PrimeSquares.UniformMajorArcBudget

open Finset Filter
namespace PrimeSquares

noncomputable def fivePeriodShifts : Finset ℤ := Icc (-2) 2

theorem fivePeriodShifts_card : fivePeriodShifts.card = 5 := by decide

theorem integerPeriodSum_five (f : ℝ → ℂ) (hs : ∀ x, 1 ≤ |x| → f x = 0)
    {x : ℝ} (hx : |x| ≤ 2) :
    integerPeriodSum f x = ∑ k ∈ fivePeriodShifts, f (x+(k : ℝ)) := by
  classical
  rw [integerPeriodSum,tsum_eq_sum (s := fivePeriodShifts)]
  intro k hk
  apply hs
  have hk' : k ≤ -3 ∨ 3 ≤ k := by
    have hn : ¬ ((-2 : ℤ) ≤ k ∧ k ≤ 2) := by simpa only [fivePeriodShifts,mem_Icc] using hk
    omega
  obtain ⟨hxl,hxu⟩ := abs_le.mp hx
  rcases hk' with h | h
  · have h' : (k : ℝ) ≤ -3 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : (3 : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem circleRationalModelTerm_five (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (r : ℚ) (hr : r ∈ Set.Ico (0 : ℚ) 1) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) :
    circleRationalModelTerm N hN χ κ β r (ξ : PrimeCircle) =
      ∑ k ∈ fivePeriodShifts, rationalMajorArcTerm N χ κ β r (ξ+(k : ℝ)) := by
  have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr.1
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr.2
  have hx : |ξ-(r : ℝ)| ≤ 2 := abs_le.mpr ⟨by linarith [hξ.1],by linarith [hξ.2]⟩
  rw [circleRationalModelTerm_real]
  change integerPeriodSum (centeredRationalSymbol N hN χ κ β r) (ξ-(r : ℝ)) = _
  rw [integerPeriodSum_five _ (centeredRationalSymbol_support N hN χ κ β r) hx]
  apply sum_congr rfl
  intro k _
  rw [show ξ-(r : ℝ)+(k : ℝ) = (ξ+(k : ℝ))-(r : ℝ) by ring,
    centeredRationalSymbol_translate]

theorem circleMajorArcModel_five (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) :
    circleMajorArcModel Γ N hN χ κ β (ξ : PrimeCircle) =
      ∑ k ∈ fivePeriodShifts, finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ)) := by
  simp only [circleMajorArcModel,ContinuousMap.sum_apply]
  calc
    _ = ∑ r ∈ Γ, ∑ k ∈ fivePeriodShifts, rationalMajorArcTerm N χ κ β r (ξ+(k : ℝ)) :=
      sum_congr rfl (fun r hr => circleRationalModelTerm_five N hN χ κ β r (hΓ r hr) hξ)
    _ = _ := by rw [sum_comm];rfl

noncomputable def realModelTailBudget (R : ℝ) : ℝ :=
  (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ))

noncomputable def circleModelTailBudget (R : ℝ) : ℝ := 5*realModelTailBudget R

noncomputable def circleApproxBudget (C R : ℝ) : ℝ :=
  (4+(2+4*Real.pi)*C)/R^5 + gaussModelConstant*R^(-(5/12 : ℝ)) + circleModelTailBudget R

theorem circleMajorArcModel_outside_norm {N : ℕ} (hN : 2 ≤ N)
    (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {R ξ : ℝ} (hR : 1 ≤ R)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R)
    (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1) (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2)
    (hout : ∀ r ∈ Γ, ∀ k ∈ fivePeriodShifts,
      R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ+(k : ℝ)-(r : ℝ)|) :
    ‖circleMajorArcModel Γ N (by omega) χ κ β (ξ : PrimeCircle)‖ ≤ circleModelTailBudget R := by
  rw [circleMajorArcModel_five Γ N (by omega) χ κ β hΓ hξ]
  calc
    _ ≤ ∑ k ∈ fivePeriodShifts, ‖finiteMajorArcModel Γ N χ κ β (ξ+(k : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ fivePeriodShifts, realModelTailBudget R := sum_le_sum (fun k hk =>
      finiteMajorArcModel_outside_norm hN Γ χ κ hβ0 hβ1 hR hΓ hden hκ (fun r hr => hout r hr k hk))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,fivePeriodShifts_card,Nat.cast_ofNat,circleModelTailBudget]

theorem eventually_circleModelTailBudget :
    ∀ᶠ R : ℝ in atTop, circleModelTailBudget R ≤ R^(-(1/3 : ℝ)) := by
  have h := eventually_affine_log_model_tail (25*(4*gaussModelConstant/Real.pi))
    (5*(4*gaussModelConstant/Real.pi)/Real.log 2)
  filter_upwards [h] with R hR
  convert hR using 1
  dsimp [circleModelTailBudget,realModelTailBudget]
  ring

theorem eventually_circleApproxBudget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ R : ℝ in atTop, circleApproxBudget C R ≤ R^(-(1/6 : ℝ)) := by
  let K := 4+(2+4*Real.pi)*C
  have hK : 0 < K := by dsimp [K];positivity
  have hG := gaussModelConstant_pos
  have hp := eventually_rpow_le_mul_rpow (by norm_num : (-5 : ℝ) < -(1/3 : ℝ)) (inv_pos.mpr hK)
  have hg := eventually_rpow_le_mul_rpow (by norm_num : -(5/12 : ℝ) < -(1/3 : ℝ)) (inv_pos.mpr hG)
  have hw := eventually_rpow_le_mul_rpow (by norm_num : -(1/3 : ℝ) < -(1/6 : ℝ))
    (by norm_num : (0 : ℝ) < 1/3)
  filter_upwards [eventually_gt_atTop (0 : ℝ),hp,hg,eventually_circleModelTailBudget,hw]
    with R hR hp hg ht hw
  have he : R^(-5 : ℝ) = (R^5)⁻¹ := by rw [Real.rpow_neg hR.le];norm_num
  have hfirst : K/R^5 ≤ R^(-(1/3 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hp hK.le
    rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] at hh
    simpa only [he,div_eq_mul_inv] using hh
  have hsecond : gaussModelConstant*R^(-(5/12 : ℝ)) ≤ R^(-(1/3 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hg hG.le
    rwa [←mul_assoc,mul_inv_cancel₀ hG.ne',one_mul] at hh
  change K/R^5+_+_ ≤ _
  linarith only [hfirst,hsecond,ht,hw]

theorem circleApproxBudget_uniform_log_rate {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      circleApproxBudget C (sourceMajorArcScale N Q) ≤
        (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_circleApproxBudget hC)
  obtain ⟨N₁,hN₁⟩ := sourceMajorArcScale_uniform_lower B
  obtain ⟨N₂,hN₂⟩ := sourceMajorArcScale_logarithmic_rate hA
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ
  exact (hB _ (hN₁ N ((le_max_left _ _).trans hN) Q)).trans
    (hN₂ N ((le_max_right _ _).trans hN) Q hQ)

end PrimeSquares
