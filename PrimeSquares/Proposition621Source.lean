import PrimeSquares.Proposition621
import PrimeSquares.SourceHighUniformGeometry
import PrimeSquares.CompactHighSourceIdentification
import PrimeSquares.SourceScaleLowEstimate

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def pageHighSymbol (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (E : Option PageZeroDatum) : C(PrimeCircle,ℂ) :=
  circleHighModel (sourceRationalCenters R) N hN (optionPageConductor 1 E) Q
    (conductorMajorant (optionPageConductor 1 E))
    (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
    (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)

theorem pageHighOperator_symbol (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (E : Option PageZeroDatum) :
    pageHighOperator N hN Q R E=integerMultiplier (pageHighSymbol N hN Q R E) := rfl

/-- Periodization of the manuscript's actual complementary narrow cutoffs,
written with the already verified reduced canonical rational enumeration. -/
noncomputable def paperPageHighFrequencyValue (N : ℕ) (Q R : ℝ) (E : Option PageZeroDatum) (ξ : ℝ) : ℂ :=
  ∑ r ∈ sourceRationalCenters R,∑' k : ℤ,rationalHighModelTerm N (optionPageConductor 1 E) Q
    (conductorMajorant (optionPageConductor 1 E))
    (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
    (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E) r (ξ+k)

theorem pageHighSymbol_paper_identity {N : ℕ} (hN : 1 ≤ N) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2)
    (E : Option PageZeroDatum) (hE : ∀ F,E=some F → (F.conductor : ℝ) ≤ R) (ξ : ℝ) :
    pageHighSymbol N hN Q R E (ξ : PrimeCircle)=paperPageHighFrequencyValue N Q R E ξ := by
  have hR : 1 ≤ R := hQ.trans hQR
  have hq : 0<optionPageConductor 1 E := by
    cases E with
    | none => norm_num [optionPageConductor]
    | some F => exact lt_of_lt_of_le (by norm_num : 0<(2 : ℕ)) F.conductor_two
  have hqR : (optionPageConductor 1 E : ℝ) ≤ R := by
    cases he : E with
    | none => simpa only [optionPageConductor_none,Nat.cast_one] using hR
    | some F => exact hE F he
  have hB : 0<conductorMajorant (optionPageConductor 1 E) :=
    lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le _ hq)
  have hQR2 : Q ≤ R^2 := hQR.trans (radius_le_square hR)
  have hWR2 := source_exceptional_squared_radius hq (by linarith : 0 ≤ Q) hQR hqR
  have hb2 : 2*(R^2)^4 ≤ (N : ℝ)^2 := by convert hb using 1;ring
  unfold pageHighSymbol paperPageHighFrequencyValue circleHighModel
  rw [ContinuousMap.sum_apply]
  apply sum_congr rfl
  intro r hr
  rw [circleHighTerm_real]
  apply tsum_congr
  intro k
  have hden : (r.den : ℝ) ≤ R^2 := ((mem_sourceRationalCenters (by linarith) r).mp hr).2.trans (radius_le_square hR)
  have h := centeredHighSymbol_source hN r hq (by linarith : 0<Q) hB hQR2 hWR2 hden hb2
    (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
    (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E) (ξ := ξ+(k : ℝ))
  simpa only [show ξ+(k : ℝ)-(r : ℝ)=ξ-(r : ℝ)+(k : ℝ) by ring] using h

theorem dyadic_tail_covers_source_scales {N₀ : ℝ} (hN₀ : 2 ≤ N₀) (k : ℕ)
    (hk : N₀ ≤ (2 : ℝ)^k) : ∃ j : ℕ,(2 : ℕ)^j*2=(2 : ℕ)^k ∧
      N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) := by
  have hk0 : 1 ≤ k := by
    by_contra h
    have hz : k=0 := by omega
    rw [hz,pow_zero] at hk
    linarith
  have he : (2 : ℕ)^(k-1)*2=(2 : ℕ)^k := by rw [←pow_succ,Nat.sub_add_cancel hk0]
  refine ⟨k-1,he,?_⟩
  rw [he]
  exact_mod_cast hk

/-- Both clauses of the actual source Proposition6.21. The allowed source
range supplies the cutoff-containment budget uniformly from every N0 >= 2.
The same c0 works for every epsilon; bounded Q has a verified uniform bound. -/
theorem proposition621_source (HP : PrimeAsymptoticInputs)
    {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) :
    ∃ c₀ : ℝ,0<c₀ ∧ ∀ ε : ℝ,0<ε → ∃ K : ℝ,0<K ∧
    ∀ Q N₀ : ℝ,2 ≤ Q → 2 ≤ N₀ → Real.log Q ≤ c₀*Real.sqrt (Real.log N₀) →
    ∀ E : ℕ → Option PageZeroDatum,
      (∀ j F,N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → E j=some F →
        (F.conductor : ℝ) ≤ sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q ∧
        1-(c/2)/Real.log (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)<F.beta) →
    ∀ f : ℓ²(ℤ,ℂ),∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,G x=⨆ j : ℕ,‖sourcePageDyadicTailOperator N₀ Q E j f x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ G x) ∧
      ‖G‖ ≤ (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q))*‖f‖ ∧
      (∀ j,‖sourcePageDyadicTailOperator N₀ Q E j f‖ ≤
        (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q))*‖f‖) ∧
      (∀ j,N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → ∀ ξ : ℝ,
        pageHighSymbol ((2 : ℕ)^j*2) (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j;omega)
          Q (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q) (E j) (ξ : PrimeCircle)=
        paperPageHighFrequencyValue ((2 : ℕ)^j*2) Q
          (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q) (E j) ξ) := by
  obtain ⟨c₀,hc₀,hgeometry⟩ := sourceHigh_uniform_geometry
  refine ⟨c₀,hc₀,?_⟩
  intro ε hε
  obtain ⟨K,hK,hmax⟩ := proposition621 HP hC hBourgain hc hPage hε
  refine ⟨K,hK,?_⟩
  intro Q N₀ hQ hN₀ hcut E hE f
  obtain ⟨G,heq,h0,ht,hn,hfixed⟩ := hmax Q hQ N₀ hN₀ E hE f
  refine ⟨G,heq,h0,ht,hn,hfixed,?_⟩
  intro j hj ξ
  apply pageHighSymbol_paper_identity _ (by linarith : 1 ≤ Q)
    (sourceMajorArcScale_cutoff_le (by linarith : 1 ≤ Q) _)
    (hgeometry Q N₀ hQ hN₀ hcut ((2 : ℕ)^j*2) hj) (E j)
    (fun F hF => (hE j F hj hF).1) ξ

end PrimeSquares
