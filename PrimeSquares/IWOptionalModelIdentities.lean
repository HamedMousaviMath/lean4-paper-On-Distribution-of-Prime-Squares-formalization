import PrimeSquares.IWCharacterModelComparison
import PrimeSquares.IWStartingScaleBudget

set_option autoImplicit false
open Finset
open scoped Classical
namespace PrimeSquares

noncomputable def largePageDatum (Q : ℝ) (E : Option PageZeroDatum) : Option PageZeroDatum :=
  E.bind (fun F => if Q<(F.conductor : ℝ) then some F else none)

theorem largePageDatum_eq_some (Q : ℝ) (E : Option PageZeroDatum) (F : PageZeroDatum) :
    largePageDatum Q E=some F ↔ E=some F ∧ Q<(F.conductor : ℝ) := by
  simp only [largePageDatum,Option.bind_eq_some_iff]
  constructor
  · rintro ⟨G,hE,hG⟩
    split_ifs at hG with hbig
    · have he : G=F := Option.some.inj hG
      subst G
      exact ⟨hE,hbig⟩
  · rintro ⟨hE,hbig⟩
    exact ⟨F,hE,by simp only [ite_eq_left hbig]⟩

noncomputable def fixedPageOriginalSymbol (N : ℕ) (hN : 1≤N) (R : ℝ)
    (E₀ E : Option PageZeroDatum) : C(PrimeCircle,ℂ) :=
  E₀.elim 0 (fun F => if E=some F then
    varyingIndexAnnularBlock (sourceRationalCenters R) N hN F.beta
      (rationalInducedSquareCoefficient F.conductor F.character) else 0)

noncomputable def fixedPageIWSymbol (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (a : ℝ) (ha : 2≤a) (E₀ E : Option PageZeroDatum) : C(PrimeCircle,ℂ) :=
  E₀.elim 0 (fun F => if E=some F then
    weightedWidthAnnularBlock Γ N hN F.beta a ha
      (rationalInducedSquareCoefficient F.conductor F.character) else 0)

noncomputable def pageIWLowSymbol (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (a : ℝ) (ha : 2≤a) (E₀ E : Option PageZeroDatum) : C(PrimeCircle,ℂ) :=
  weightedWidthAnnularBlock Γ N hN 1 a ha rationalPrincipalGauss-
    fixedPageIWSymbol Γ N hN a ha E₀ E

theorem induced_annular_mask (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) :
    varyingIndexAnnularBlock Γ N hN β (rationalInducedSquareCoefficient q χ)=
      varyingIndexAnnularBlock (Γ.filter (fun t => q∣t.den)) N hN β
        (fun t => rationalTwistedGauss t (sourceInducedCharacter q χ t)) := by
  classical
  unfold varyingIndexAnnularBlock
  rw [sum_filter]
  apply sum_congr rfl
  intro t _
  unfold rationalInducedSquareCoefficient
  by_cases hd : q∣t.den
  · simp only [ite_eq_left hd]
  · simp only [ite_eq_right hd]
    ext ξ
    change (0 : ℂ)*_=0
    exact zero_mul _

theorem pageExceptionalAnnularSymbol_some (N : ℕ) (hN : 1≤N) (R : ℝ) (F : PageZeroDatum) :
    pageExceptionalAnnularSymbol N hN R (some F)=
      varyingIndexAnnularBlock (sourceRationalCenters R) N hN F.beta
        (rationalInducedSquareCoefficient F.conductor F.character) := by
  exact (induced_annular_mask _ _ _ _ _ _).symm

theorem page_exceptional_small_large_split {Q : ℝ} (N : ℕ) (hN : 1≤N) (R : ℝ)
    (E₀ E : Option PageZeroDatum) (hsmall : ∀ F,E₀=some F → (F.conductor : ℝ)≤Q)
    (hselected : ∀ F,E=some F → (F.conductor : ℝ)≤Q → E₀=some F) :
    pageExceptionalAnnularSymbol N hN R E=fixedPageOriginalSymbol N hN R E₀ E+
      pageExceptionalAnnularSymbol N hN R (largePageDatum Q E) := by
  classical
  cases E with
  | none =>
    cases E₀ <;> simp [pageExceptionalAnnularSymbol,fixedPageOriginalSymbol,largePageDatum]
  | some F =>
    by_cases hF : Q<(F.conductor : ℝ)
    · have hno : E₀≠some F := by
        intro h
        exact (not_lt_of_ge (hsmall F h)) hF
      cases E₀ with
      | none => simp [largePageDatum,fixedPageOriginalSymbol,hF]
      | some G =>
        have hFG : F≠G := by
          intro h
          subst G
          exact hno rfl
        simp [largePageDatum,fixedPageOriginalSymbol,hF,hFG]
    · have h₀ := hselected F rfl (le_of_not_gt hF)
      rw [h₀]
      simp [largePageDatum,hF,fixedPageOriginalSymbol,pageExceptionalAnnularSymbol_some]
      rfl

theorem page_model_IW_difference (N : ℕ) (hN : 1≤N) (R : ℝ) (Γ : Finset ℚ)
    (a : ℝ) (ha : 2≤a) {Q : ℝ} (E₀ E : Option PageZeroDatum)
    (hsmall : ∀ F,E₀=some F → (F.conductor : ℝ)≤Q)
    (hselected : ∀ F,E=some F → (F.conductor : ℝ)≤Q → E₀=some F) :
    circleMajorArcModel (sourceRationalCenters R) N hN
      (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
      (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)-
      pageIWLowSymbol Γ N hN a ha E₀ E=
      (varyingIndexAnnularBlock (sourceRationalCenters R) N hN 1 rationalPrincipalGauss-
        weightedWidthAnnularBlock Γ N hN 1 a ha rationalPrincipalGauss)-
      (fixedPageOriginalSymbol N hN R E₀ E-fixedPageIWSymbol Γ N hN a ha E₀ E)-
        pageExceptionalAnnularSymbol N hN R (largePageDatum Q E) := by
  rw [pageCircleModel_annular_decomposition,
    page_exceptional_small_large_split N hN R E₀ E hsmall hselected,pageIWLowSymbol]
  abel

theorem fixedPageIWSymbol_actual_measure {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 2≤a) (F : PageZeroDatum)
    (hF : F.conductor≤Q) (E : Option PageZeroDatum) :
    fixedPageIWSymbol (iwFrequencySet d.S k) N hN a ha (some F) E=
      if E=some F then weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN F.beta a ha
        (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period
          (DirichletCharacter.changeLevel (iw_period_divisible_small d F.conductor_two hF) F.character)))
      else 0 := by
  classical
  simp only [fixedPageIWSymbol,Option.elim_some]
  by_cases he : E=some F
  · simp only [ite_eq_left he]
    exact (iw_induced_width_symbol d _ F.character F.primitive N hN F.beta a ha).symm
  · simp only [ite_eq_right he]

end PrimeSquares
