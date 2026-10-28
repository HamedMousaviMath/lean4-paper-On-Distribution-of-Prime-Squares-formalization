import PrimeSquares.IWActualAnnularSymbols
import PrimeSquares.IWLargeConductorMaximum
import PrimeSquares.FiniteCircleModel

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem circleRationalModelTerm_annular_decomposition (N : ℕ) (hN : 1≤N)
    (χ : (r : ℚ) → DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    circleRationalModelTerm N hN χ κ β r=
      rationalPrincipalGauss r • circleAnnularSource N hN 1 (Nat.log2 r.den) r-
      (κ r*rationalTwistedGauss r (χ r)) • circleAnnularSource N hN β (Nat.log2 r.den) r := by
  ext θ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) (θ-((r : ℝ) : PrimeCircle)) : ℝ)
  change compactPeriodWindow (centeredRationalSymbol N hN χ κ β r) x=
    rationalPrincipalGauss r*compactPeriodWindow (localizedAnnularSource N hN 1 (Nat.log2 r.den)) x-
    (κ r*rationalTwistedGauss r (χ r))*compactPeriodWindow (localizedAnnularSource N hN β (Nat.log2 r.den)) x
  simp only [compactPeriodWindow,centeredRationalSymbol,ContinuousMap.coe_mk,
    localizedAnnularGaussModel,annularGaussModel,localizedAnnularSource,annularCutoffSymbol,
    rationalPrincipalGauss,rationalTwistedGauss,sourceArcCutoffScale]
  ring

theorem circleMajorArcModel_annular_decomposition (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (χ : (r : ℚ) → DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleMajorArcModel Γ N hN χ κ β=
      varyingIndexAnnularBlock Γ N hN 1 rationalPrincipalGauss-
      varyingIndexAnnularBlock Γ N hN β (fun r => κ r*rationalTwistedGauss r (χ r)) := by
  simp only [circleMajorArcModel,varyingIndexAnnularBlock,←sum_sub_distrib]
  exact sum_congr rfl (fun r _ => circleRationalModelTerm_annular_decomposition N hN χ κ β r)

theorem pageCircleModel_annular_decomposition (N : ℕ) (hN : 1≤N) (R : ℝ)
    (E : Option PageZeroDatum) :
    circleMajorArcModel (sourceRationalCenters R) N hN
      (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
      (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)=
      varyingIndexAnnularBlock (sourceRationalCenters R) N hN 1 rationalPrincipalGauss-
        pageExceptionalAnnularSymbol N hN R E := by
  rw [circleMajorArcModel_annular_decomposition]
  cases E with
  | none =>
    ext θ
    simp [sourceExceptionalSelector,optionPageConductor,optionPageCharacter,optionPageBeta,
      varyingIndexAnnularBlock,pageExceptionalAnnularSymbol,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul]
  | some F =>
    congr 1
    ext θ
    simp [optionPageConductor,optionPageCharacter,optionPageBeta,sourceExceptionalSelector,
      pageExceptionalAnnularSymbol,varyingIndexAnnularBlock,sum_filter,ContinuousMap.sum_apply,
      ite_mul]
    apply sum_congr rfl
    intro t _
    by_cases hd : F.conductor∣t.den
    · simp only [ite_eq_left hd]
    · simp only [ite_eq_right hd]
      change (0 : ℂ)*_=0
      exact zero_mul _

theorem iw_small_frequency_set {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) :
    (iwFrequencySet d.S k).filter (fun r => r.den≤Q)=canonicalRationalCenters Q := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hr,hd⟩ := mem_filter.mp hr
    exact (mem_canonicalRationalCenters _ _).mpr ⟨((iwFrequencySet_mem d.positive r).mp hr).1,hd⟩
  · intro hr
    exact mem_filter.mpr ⟨d.covered hr,((mem_canonicalRationalCenters _ _).mp hr).2⟩

theorem source_small_frequency_set {Q : ℕ} {R : ℝ} (hQR : (Q : ℝ)≤R) :
    (sourceRationalCenters R).filter (fun r => r.den≤Q)=canonicalRationalCenters Q := by
  classical
  have hR : 0≤R := (Nat.cast_nonneg Q).trans hQR
  ext r
  simp only [mem_filter,mem_sourceRationalCenters hR,mem_canonicalRationalCenters]
  constructor
  · rintro ⟨⟨hr,_⟩,hd⟩
    exact ⟨hr,hd⟩
  · rintro ⟨hr,hd⟩
    exact ⟨⟨hr,(by exact_mod_cast hd : (r.den : ℝ)≤Q).trans hQR⟩,hd⟩

theorem iw_original_common_comparison {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) {R : ℝ} (hQR : (Q : ℝ)≤R)
    (N : ℕ) (hN : 1≤N) (β a : ℝ) (ha : 2≤a) (c : ℚ → ℂ) :
    varyingIndexAnnularBlock (sourceRationalCenters R) N hN β c-
      weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha c=
      varyingIndexAnnularBlock ((sourceRationalCenters R).filter (fun r => Q<r.den)) N hN β c-
      weightedWidthAnnularBlock ((iwFrequencySet d.S k).filter (fun r => Q<r.den)) N hN β a ha c+
      (varyingIndexAnnularBlock (canonicalRationalCenters Q) N hN β c-
        weightedWidthAnnularBlock (canonicalRationalCenters Q) N hN β a ha c) := by
  classical
  have ho : varyingIndexAnnularBlock (sourceRationalCenters R) N hN β c=
      varyingIndexAnnularBlock (canonicalRationalCenters Q) N hN β c+
      varyingIndexAnnularBlock ((sourceRationalCenters R).filter (fun r => Q<r.den)) N hN β c := by
    have h := sum_filter_add_sum_filter_not (sourceRationalCenters R) (fun r => r.den≤Q)
      (fun r => c r • circleAnnularSource N hN β (Nat.log2 r.den) r)
    simpa only [not_le,source_small_frequency_set hQR,varyingIndexAnnularBlock] using h.symm
  have hl : weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha c=
      weightedWidthAnnularBlock (canonicalRationalCenters Q) N hN β a ha c+
      weightedWidthAnnularBlock ((iwFrequencySet d.S k).filter (fun r => Q<r.den)) N hN β a ha c := by
    have h := sum_filter_add_sum_filter_not (iwFrequencySet d.S k) (fun r => r.den≤Q)
      (fun r => c r • circleWidthAnnular N hN β a ha r)
    simpa only [not_le,iw_small_frequency_set d,weightedWidthAnnularBlock] using h.symm
  rw [ho,hl]
  abel

end PrimeSquares
