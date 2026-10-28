import PrimeSquares.FiniteMajorArcModels
import PrimeSquares.RationalArcOverlap
import PrimeSquares.MajorArcGeometry
import PrimeSquares.ExponentialMajorArcBudget
import PrimeSquares.SourceModelLogarithmicRate

/-!
# Pointwise error of the finite genuine model on a rational major arc

The analytic caller uses the already proved R^-5 implication from the raw
progression-prefix estimate. No source minor-arc conclusion is assumed.
-/

open Finset Filter

namespace PrimeSquares

noncomputable def gaussModelConstant : ℝ :=
  Classical.choose annularGaussModel_uniform_bounds

theorem gaussModelConstant_pos : 0 < gaussModelConstant :=
  (Classical.choose_spec annularGaussModel_uniform_bounds).1

theorem rationalMajorArcTerm_outside_norm {N : ℕ} (hN : 2 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℚ) {ξ R : ℝ}
    (hκ : ‖κ r‖ ≤ 1) (hden : (r.den : ℝ) ≤ R)
    (hξ : R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)|) :
    ‖rationalMajorArcTerm N χ κ β r ξ‖ ≤
      (4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  have hb := ((Classical.choose_spec annularGaussModel_uniform_bounds).2
    N r.den (χ r) (κ r) β (r.num : ZMod r.den) hN hβ0 hβ1 ha hκ).2
      R hden (ξ-(r : ℝ)) hξ
  rw [rationalMajorArcTerm_eq_localized]
  exact (localizedAnnularGaussModel_norm_le N r.den (χ r) (κ r) β
    (r.num : ZMod r.den) (Nat.log2 r.den) (ξ-(r : ℝ))).trans hb

theorem finiteMajorArcModel_active_norm (Γ : Finset ℚ) (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β ξ B : ℝ)
    (hterm : ∀ r ∈ Γ,
      sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) ≠ 0 →
      ‖rationalMajorArcTerm N χ κ β r ξ‖ ≤ B) :
    ‖finiteMajorArcModel Γ N χ κ β ξ‖ ≤ ((activeRationalCenters Γ ξ).card : ℝ)*B := by
  classical
  have hsub : activeRationalCenters Γ ξ ⊆ Γ := filter_subset _ _
  have he : (∑ r ∈ activeRationalCenters Γ ξ, rationalMajorArcTerm N χ κ β r ξ) =
      ∑ r ∈ Γ, rationalMajorArcTerm N χ κ β r ξ := by
    apply sum_subset hsub
    intro r hr hn
    have hz : sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) = 0 := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hr, h⟩)
    simp only [rationalMajorArcTerm, hz, Complex.ofReal_zero, mul_zero]
  rw [finiteMajorArcModel, ← he]
  calc
    _ ≤ ∑ r ∈ activeRationalCenters Γ ξ, ‖rationalMajorArcTerm N χ κ β r ξ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ activeRationalCenters Γ ξ, B := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hrΓ, hactive⟩ := mem_filter.mp hr
      exact hterm r hrΓ hactive
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem finiteMajorArcModel_outside_norm {N : ℕ} (hN : 2 ≤ N)
    (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {R ξ : ℝ} (hR : 1 ≤ R)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1)
    (hout : ∀ r ∈ Γ, R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)|) :
    ‖finiteMajorArcModel Γ N χ κ β ξ‖ ≤
      (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) := by
  have hB : 0 ≤ (4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) := by
    have hc := gaussModelConstant_pos
    positivity
  calc
    _ ≤ ((activeRationalCenters Γ ξ).card : ℝ) *
        ((4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ))) :=
      finiteMajorArcModel_active_norm Γ N χ κ β ξ _ (fun r hr _ =>
        rationalMajorArcTerm_outside_norm hN χ κ hβ0 hβ1 r (hκ r hr) (hden r hr) (hout r hr))
    _ ≤ (5+Real.log R/Real.log 2) *
        ((4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ))) :=
      mul_le_mul_of_nonneg_right (activeRationalCenters_real_card Γ ξ hR hΓ hden) hB
    _ = _ := by ring

theorem finiteMajorArcError_major_arc {N : ℕ} (hN : 2 ≤ N)
    (Γ : Finset ℚ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {R ξ δ : ℝ} (hR : 1 ≤ R)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1)
    {r₀ : ℚ} (hr₀ : r₀ ∈ Γ)
    (hsep : 2*R^3 < (N : ℝ)^2) (hcore : 2*R^4 ≤ (N : ℝ)^2)
    (hξ : |ξ-(r₀ : ℝ)| ≤ R/((r₀.den : ℝ)*(N : ℝ)^2))
    (hmain : ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
      (rationalOrdinaryModelTerm N r₀ ξ + rationalExceptionalModelTerm N χ κ β r₀ ξ)‖ ≤ δ) :
    ‖finiteMajorArcError Γ N χ κ β ξ‖ ≤
      δ + (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  have hRp : 0 < R := by linarith
  have hcut := rationalMajorArc_cutoff_core (by omega : 1 ≤ N) (hden r₀ hr₀) hcore hξ
  have hterm := rationalMajorArcTerm_core N χ κ β r₀ ξ hcut
  have hsum : rationalMajorArcTerm N χ κ β r₀ ξ +
      finiteMajorArcModel (Γ.erase r₀) N χ κ β ξ = finiteMajorArcModel Γ N χ κ β ξ := by
    exact add_sum_erase Γ (fun r => rationalMajorArcTerm N χ κ β r ξ) hr₀
  have hout : ∀ r ∈ Γ.erase r₀, R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)| := by
    intro r hr
    obtain ⟨hne, hrΓ⟩ := mem_erase.mp hr
    exact (rationalMajorArc_other_outside hRp hNp hsep (hden r₀ hr₀) (hden r hrΓ) hne hξ).le
  have htail := finiteMajorArcModel_outside_norm hN (Γ.erase r₀) χ κ hβ0 hβ1 hR
    (fun r hr => hΓ r (mem_erase.mp hr).2)
    (fun r hr => hden r (mem_erase.mp hr).2)
    (fun r hr => hκ r (mem_erase.mp hr).2) hout
  have he : finiteMajorArcError Γ N χ κ β ξ =
      (annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
        (rationalOrdinaryModelTerm N r₀ ξ + rationalExceptionalModelTerm N χ κ β r₀ ξ)) -
      finiteMajorArcModel (Γ.erase r₀) N χ κ β ξ := by
    rw [finiteMajorArcError, ← hsum, hterm]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hmain htail)

theorem finiteMajorArcError_from_prefix {N : ℕ} (hN : 2 ≤ N)
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
    ‖finiteMajorArcError Γ N χ κ β ξ‖ ≤
      (4+(2+4*Real.pi)*C)/R^5 +
        (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) := by
  let : NeZero r₀.den := ⟨r₀.den_pos.ne'⟩
  have hRpow : R ≤ R^(11/10 : ℝ) := by
    calc
      R = R^(1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hq : (r₀.den : ℝ) ≤ R^(11/10 : ℝ) := (hden r₀ hr₀).trans hRpow
  have hsource := annularMangoldt_majorArc_inverse_fifth (by omega : 1 ≤ N)
    (χ r₀) (κ r₀) hβ0 r₀.num (ξ-(r₀ : ℝ)) hR hC hq hξ hlog hbudget hexp hprefix
  rw [rationalCenter_add_offset] at hsource
  have hmain :
      ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
        (rationalOrdinaryModelTerm N r₀ ξ + rationalExceptionalModelTerm N χ κ β r₀ ξ)‖ ≤
        (4+(2+4*Real.pi)*C)/R^5 := by
    simpa only [rationalOrdinaryModelTerm, rationalExceptionalModelTerm, sub_eq_add_neg] using hsource
  exact finiteMajorArcError_major_arc hN Γ χ κ hβ0.le hβ1 hR hΓ hden hκ hr₀ hsep hcore hξ hmain


theorem eventually_finiteMajorArcBudget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ R : ℝ in atTop,
      (4+(2+4*Real.pi)*C)/R^5 +
        (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) ≤
      R^(-(1/6 : ℝ)) := by
  let K := 4+(2+4*Real.pi)*C
  have hK : 0 < K := by dsimp [K]; positivity
  have hp := eventually_rpow_le_mul_rpow (by norm_num : (-5 : ℝ) < -(1/3 : ℝ))
    (inv_pos.mpr hK)
  have ht := eventually_affine_log_model_tail (5*(4*gaussModelConstant/Real.pi))
    ((4*gaussModelConstant/Real.pi)/Real.log 2)
  have hw := eventually_rpow_le_mul_rpow (by norm_num : -(1/3 : ℝ) < -(1/6 : ℝ))
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hp, ht, hw] with R hR hp ht hw
  have he : R^(-5 : ℝ) = (R^5)⁻¹ := by
    rw [Real.rpow_neg hR.le]
    norm_num
  have hfirst : K/R^5 ≤ R^(-(1/3 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hp hK.le
    rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at hh
    simpa only [he, div_eq_mul_inv] using hh
  have htail :
      (5+Real.log R/Real.log 2)*(4*gaussModelConstant/Real.pi)*R^(-(5/12 : ℝ)) ≤
        R^(-(1/3 : ℝ)) := by
    convert ht using 1
    ring
  change K/R^5 + _ ≤ _
  linarith only [hfirst, htail, hw]

end PrimeSquares
