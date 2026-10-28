import PrimeSquares.QuadraticWeylInput
import PrimeSquares.WeightedAnnularBlockBounds
import PrimeSquares.PowerDecayingAnnularMaximum

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def fullSquareRationalModelTerm (N : ℕ) (r : ℚ) (ξ : ℝ) : ℂ :=
  rationalFullSquareGauss r*annularOscillatoryModel N 1 (ξ-(r : ℝ))*
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)))

noncomputable def fullSquareFiniteModel (Γ : Finset ℚ) (N : ℕ) (ξ : ℝ) : ℂ :=
  ∑ r ∈ Γ, fullSquareRationalModelTerm N r ξ

noncomputable def fullSquareRealTailBudget (R : ℝ) : ℝ :=
  (5+Real.log R/Real.log 2)*(4/(Real.pi*Real.sqrt R))

theorem fullSquareRationalModelTerm_norm (N : ℕ) (r : ℚ) (ξ : ℝ) :
    ‖fullSquareRationalModelTerm N r ξ‖ ≤
      ‖rationalFullSquareGauss r‖*‖annularOscillatoryModel N 1 (ξ-(r : ℝ))‖ := by
  rw [fullSquareRationalModelTerm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) := sourceArcCutoff_nonneg _
  have h1 : sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) ≤ 1 := sourceArcCutoff_le_one _
  rw [abs_of_nonneg h0]
  exact (mul_le_mul_of_nonneg_left h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_one _)

theorem fullSquareRationalModelTerm_outside {N : ℕ} (hN : 2 ≤ N) {R ξ : ℝ}
    (hR : 0 < R) (r : ℚ) (hd : (r.den : ℝ) ≤ R)
    (hout : R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)|) :
    ‖fullSquareRationalModelTerm N r ξ‖ ≤ 4/(Real.pi*Real.sqrt R) := by
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsd : 0 < Real.sqrt (r.den : ℝ) := Real.sqrt_pos.mpr hd0
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsd2 := Real.sq_sqrt hd0.le
  have hsR2 := Real.sq_sqrt hR.le
  calc
    _ ≤ ‖rationalFullSquareGauss r‖*‖annularOscillatoryModel N 1 (ξ-(r : ℝ))‖ :=
      fullSquareRationalModelTerm_norm N r ξ
    _ ≤ (2*(Real.sqrt (r.den : ℝ))⁻¹)*(2*(r.den : ℝ)/(Real.pi*R)) :=
      mul_le_mul (rationalFullSquareGauss_half_decay r)
        (annularOscillatoryModel_outside_arc hN (by norm_num) (by norm_num) hd0 hR hout)
        (norm_nonneg _) (by positivity)
    _ = (4/(Real.pi*R))*Real.sqrt (r.den : ℝ) := by field_simp; nlinarith
    _ ≤ (4/(Real.pi*R))*Real.sqrt R := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) (by positivity)
    _ = _ := by field_simp; nlinarith

theorem fullSquareFiniteModel_active_norm (Γ : Finset ℚ) (N : ℕ) (ξ B : ℝ)
    (hterm : ∀ r ∈ Γ, sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) ≠ 0 →
      ‖fullSquareRationalModelTerm N r ξ‖ ≤ B) :
    ‖fullSquareFiniteModel Γ N ξ‖ ≤ ((activeRationalCenters Γ ξ).card : ℝ)*B := by
  classical
  have hsub : activeRationalCenters Γ ξ ⊆ Γ := filter_subset _ _
  have he : (∑ r ∈ activeRationalCenters Γ ξ, fullSquareRationalModelTerm N r ξ) =
      ∑ r ∈ Γ, fullSquareRationalModelTerm N r ξ := by
    apply sum_subset hsub
    intro r hr hn
    have hz : sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) = 0 := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hr, h⟩)
    simp only [fullSquareRationalModelTerm, hz, Complex.ofReal_zero, mul_zero]
  rw [fullSquareFiniteModel, ←he]
  calc
    _ ≤ ∑ r ∈ activeRationalCenters Γ ξ, ‖fullSquareRationalModelTerm N r ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ activeRationalCenters Γ ξ, B := sum_le_sum (fun r hr =>
      hterm r (mem_filter.mp hr).1 (mem_filter.mp hr).2)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem fullSquareFiniteModel_outside {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    {R ξ : ℝ} (hR : 1 ≤ R) (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ R)
    (hout : ∀ r ∈ Γ, R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)|) :
    ‖fullSquareFiniteModel Γ N ξ‖ ≤ fullSquareRealTailBudget R := by
  have hRp : 0 < R := by linarith
  calc
    _ ≤ ((activeRationalCenters Γ ξ).card : ℝ)*(4/(Real.pi*Real.sqrt R)) :=
      fullSquareFiniteModel_active_norm Γ N ξ _ (fun r hr _ =>
        fullSquareRationalModelTerm_outside hN hRp r (hd r hr) (hout r hr))
    _ ≤ (5+Real.log R/Real.log 2)*(4/(Real.pi*Real.sqrt R)) :=
      mul_le_mul_of_nonneg_right (activeRationalCenters_real_card Γ ξ hR hΓ hd) (by positivity)
    _ = _ := rfl

theorem fullSquareCircleModel_five (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) :
    varyingIndexAnnularBlock Γ N hN 1 rationalFullSquareGauss (ξ : PrimeCircle) =
      ∑ k ∈ fivePeriodShifts, fullSquareFiniteModel Γ N (ξ+(k : ℝ)) := by
  simp only [varyingIndexAnnularBlock, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    _ = ∑ r ∈ Γ, ∑ k ∈ fivePeriodShifts, fullSquareRationalModelTerm N r (ξ+(k : ℝ)) := by
      apply sum_congr rfl
      intro r hr
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast (hΓ r hr).1
      have hr1 : (r : ℝ) < 1 := by exact_mod_cast (hΓ r hr).2
      have hx : |ξ-(r : ℝ)| ≤ 2 := abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      rw [circleAnnularSource_real]
      change rationalFullSquareGauss r*integerPeriodSum (localizedAnnularSource N hN 1 (Nat.log2 r.den))
        (ξ-(r : ℝ)) = _
      rw [integerPeriodSum_five _ (localizedAnnularSource_support N hN 1 _) hx, mul_sum]
      apply sum_congr rfl
      intro k _
      unfold localizedAnnularSource fullSquareRationalModelTerm
      rw [show ξ-(r : ℝ)+(k : ℝ) = (ξ+(k : ℝ))-(r : ℝ) by ring]
      change rationalFullSquareGauss r*(annularOscillatoryModel N 1 ((ξ+(k : ℝ))-(r : ℝ))*
        Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) ((ξ+(k : ℝ))-(r : ℝ)))) = _
      ring
    _ = _ := by rw [sum_comm]; rfl

theorem fullSquareCircleModel_outside {N : ℕ} (hN : 2 ≤ N) {R ξ : ℝ} (hR : 1 ≤ R)
    (hξ : ξ ∈ Set.Icc (-1 : ℝ) 2) (hout : OutsideSourceMajorArcs N R ξ) :
    ‖varyingIndexAnnularBlock (sourceRationalCenters R) N (by omega) 1 rationalFullSquareGauss
      (ξ : PrimeCircle)‖ ≤ 5*fullSquareRealTailBudget R := by
  have hindex := fun r hr => (mem_sourceRationalCenters (by linarith : 0 ≤ R) r).mp hr
  rw [fullSquareCircleModel_five _ N (by omega) (fun r hr => (hindex r hr).1) hξ]
  calc
    _ ≤ ∑ k ∈ fivePeriodShifts, ‖fullSquareFiniteModel (sourceRationalCenters R) N (ξ+(k : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ fivePeriodShifts, fullSquareRealTailBudget R := sum_le_sum (fun k _ =>
      fullSquareFiniteModel_outside hN _ hR (fun r hr => (hindex r hr).1)
        (fun r hr => (hindex r hr).2) (fun r hr => hout r hr k))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, fivePeriodShifts_card, Nat.cast_ofNat]

end PrimeSquares
