import PrimeSquares.ActualPageHighMaximum
import PrimeSquares.SharpHighMaximalAsymptotic
import PrimeSquares.TemporalMaximumNorm
import PrimeSquares.FiniteOperatorEnvelope
import PrimeSquares.MajorArcParameters

open scoped lp
namespace PrimeSquares

theorem exact_maximum_of_majorant (F : ℕ → ℓ²(ℤ,ℂ)) (g : lp (fun _ : ℤ => ℝ) 2)
    (hg : ∀ x,0 ≤ g x) (hdom : ∀ j x,‖F j x‖ ≤ g x) :
    ∃ G : lp (fun _ : ℤ => ℝ) 2,(∀ x,G x=⨆ j : ℕ,‖F j x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖F j x‖ ≤ G x) ∧ ‖G‖ ≤ ‖g‖ := by
  have hfinite : FiniteTemporalMajorants F ‖g‖ := fun _ => ⟨g,hg,fun j _ x => hdom j x,le_rfl⟩
  have hb (x : ℤ) : BddAbove (Set.range (fun j : ℕ => ‖F j x‖)) :=
    ⟨g x,by rintro _ ⟨j,rfl⟩;exact hdom j x⟩
  refine ⟨temporalMaximumL2 F (norm_nonneg g) hfinite,fun _ => rfl,?_,?_,
    temporalMaximumL2_norm F (norm_nonneg g) hfinite⟩
  · intro x
    exact (norm_nonneg (F 0 x)).trans (le_ciSup (hb x) 0)
  · intro j x
    exact le_ciSup (hb x) j

theorem norm_le_nonnegative_majorant (v : ℓ²(ℤ,ℂ)) (g : lp (fun _ : ℤ => ℝ) 2)
    (hg : ∀ x,0 ≤ g x) (hdom : ∀ x,‖v x‖ ≤ g x) : ‖v‖ ≤ ‖g‖ := by
  rw [←magnitudeL2_norm v]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change |‖v x‖| ≤ |g x|
  rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (hg x)]
  exact hdom x

noncomputable def sourcePageDyadicTailOperator (N₀ Q : ℝ) (E : ℕ → Option PageZeroDatum)
    (j : ℕ) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  if N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) then
    pageHighOperator ((2 : ℕ)^j*2) (by have h := dyadic_annular_scale_lower (M := 2) (by norm_num) j;omega)
      Q (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q) (E j)
  else 0

/-- Both estimates in Proposition6.21, in precise epsilon form for large Q.
The dyadic family is restricted by the actual starting threshold N0. The
constant and Q cutoff are independent of N0 and all compatible source data.
The bounded-Q completion is recorded separately. -/
theorem proposition621_maximal_asymptotic (HP : PrimeAsymptoticInputs)
    {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) {ε : ℝ} (hε : 0<ε) :
    ∃ Q₀ K : ℝ,16 ≤ Q₀ ∧ 0<K ∧ ∀ Q : ℝ,Q₀ ≤ Q → ∀ N₀ : ℝ,2 ≤ N₀ →
    ∀ E : ℕ → Option PageZeroDatum,
      (∀ j F,N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → E j=some F →
        (F.conductor : ℝ) ≤ sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q ∧
        1-(c/2)/Real.log (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)<F.beta) →
    ∀ f : ℓ²(ℤ,ℂ),∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,G x=⨆ j : ℕ,‖sourcePageDyadicTailOperator N₀ Q E j f x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ G x) ∧
      ‖G‖ ≤ (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)))*‖f‖ ∧
      (∀ j,‖sourcePageDyadicTailOperator N₀ Q E j f‖ ≤
        (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)))*‖f‖) := by
  classical
  obtain ⟨Qa,Da,hQa,hDa,hActual⟩ := actualPageHigh_maximum hC hBourgain hc hPage
  obtain ⟨Qb,Db,hQb,hDb,hRate⟩ := sharpHighMaximalRate_asymptotic HP hε
  refine ⟨max Qa Qb,Da*Db,hQa.trans (le_max_left _ _),by positivity,?_⟩
  intro Q hQ N₀ _ E hE f
  obtain ⟨hL,hSlope,hrate⟩ := hRate Q ((le_max_right _ _).trans hQ)
  let E' := fun j => if N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) then E j else none
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q
  have hE' : ∀ j F,E' j=some F → PageConductorEligible c F := by
    intro j F hj
    by_cases hvalid : N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ)
    · have hF : E j=some F := by simpa only [E',ite_eq_left hvalid] using hj
      exact page_source_region_eligible hc F (hE j F hvalid hF).1 (hE j F hvalid hF).2
    · simp only [E',ite_eq_right hvalid] at hj
      cases hj
  obtain ⟨g,hg,ht,hn⟩ := hActual Q ((le_max_left _ _).trans hQ) hL hSlope 2 (by norm_num)
    E' hE' R (fun j => (sourceMajorArcScale_pos _ _).le) f
  have hdom : ∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ g x := by
    intro j x
    by_cases hvalid : N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ)
    · simpa only [sourcePageDyadicTailOperator,ite_eq_left hvalid,E',R] using ht j x
    · simpa only [sourcePageDyadicTailOperator,ite_eq_right hvalid,zero_apply,lp.coeFn_zero,
        Pi.zero_apply,norm_zero] using hg x
  have hbound : ‖g‖ ≤ ((Da*Db)*Q^(-(1/2 : ℝ))*
      Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)))*‖f‖ := by
    have h := hn.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrate hDa.le) (norm_nonneg f))
    convert h using 1;ring
  obtain ⟨G,hGeq,hG0,hGt,hGn⟩ := exact_maximum_of_majorant
    (fun j => sourcePageDyadicTailOperator N₀ Q E j f) g hg hdom
  refine ⟨G,hGeq,hG0,hGt,hGn.trans hbound,?_⟩
  intro j
  exact (norm_le_nonnegative_majorant _ G hG0 (hGt j)).trans (hGn.trans hbound)

end PrimeSquares
