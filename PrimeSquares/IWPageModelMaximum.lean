import PrimeSquares.IWOptionalModelIdentities

set_option autoImplicit false
open Finset
open scoped lp Classical
namespace PrimeSquares

/-- A quantitative comparison for the actual circle model with genuine
varying optional Page data. The fixed small character is constructed. -/
theorem iw_page_model_maximum {Cb c : ℝ} (hCb : 0≤Cb) (HB : SmoothCircleBourgainInput Cb)
    (hc : 0<c) (HP : RawPageUniquenessInput c) :
    ∃ K : ℝ,0<K ∧ ∀ (C : ℝ) (hC : 2≤C) (r k Q M : ℕ) (hr : 2≤r) (_hk : 4≤k)
      (_hQ : 2^k≤Q) (hM : 2≤M) (d : TaoArcConstructionData C (iwRho k) k Q),
      ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ)≤(M : ℝ)^2 →
      ∀ (E : ℕ → Option PageZeroDatum) (R : ℕ → ℝ),(∀ j,(Q : ℝ)≤R j) →
      (∀ j F,E j=some F → (F.conductor : ℝ)≤R j ∧ 1-(c/2)/Real.log (R j)<F.beta) →
      ∃ E₀ : Option PageZeroDatum,
        (∀ F,E₀=some F → (F.conductor : ℝ)≤Q ∧ ∃ j,E j=some F) ∧
        (∀ j F,E j=some F → (F.conductor : ℝ)≤Q → E₀=some F) ∧
        ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
          (∀ j x,‖integerMultiplier
            (circleMajorArcModel (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
              (by have h := dyadic_annular_scale_lower hM j;omega)
              (sourceInducedCharacter (optionPageConductor 1 (E j)) (optionPageCharacter 1 (E j)))
              (sourceExceptionalSelector (optionPageConductor 1 (E j)) (E j).isSome) (optionPageBeta (E j))-
            pageIWLowSymbol (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
              (by have h := dyadic_annular_scale_lower hM j;omega) (iwCutoffScale C r k Q)
              (by have h := iwCutoffScale_four_le hC hr k Q;linarith) E₀ (E j)) f x‖≤g x) ∧
          ‖g‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨A,hA,hGauss⟩ := rationalInducedSquareCoefficient_uniform_decay (by norm_num : (3/8 : ℝ)<1/2)
  obtain ⟨KL,hKL,hLarge⟩ := iw_large_conductor_maximum hCb HB hc HP
  let K₀ := 2*annularPowerConstant Cb (1/8)*A+24/Real.pi
  have hK₀ : 0<K₀ := by
    have hP := annularPowerConstant_pos hCb (1/8)
    dsimp [K₀]
    positivity
  refine ⟨2*K₀+KL,by positivity,?_⟩
  intro C hC r k Q M hr hk hQ hM d hbudget E R hR hE
  have h16 : 16≤2^k := by
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ2 : (2 : ℝ)≤Q := by exact_mod_cast (show 2≤Q by omega)
  have hQ0 : (0 : ℝ)<Q := by linarith
  have hR0 : ∀ j,0≤R j := fun j => hQ0.le.trans (hR j)
  let a := iwCutoffScale C r k Q
  have ha : 4≤a := iwCutoffScale_four_le hC hr k Q
  obtain ⟨E₀,h₀,hselected⟩ := fixed_small_page_datum hc HP hQ2 E R hR (fun j F hF => (hE j F hF).2)
  refine ⟨E₀,h₀,hselected,?_⟩
  intro f
  obtain ⟨go,hgo,hto,hno⟩ := iw_quantitative_model_comparison hC hCb HB hA.le hr hk hQ hM d hbudget
    (fun _ => 1) (fun _ => by norm_num) (fun _ => le_rfl) rationalPrincipalGauss
    (fun t _ => (hGauss t).1) (fun t _ => rationalPrincipalGauss_norm_one t) R hR f
  have hex : ∃ gs : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤gs x) ∧
      (∀ j x,‖integerMultiplier
        (fixedPageOriginalSymbol ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (R j) E₀ (E j)-
        fixedPageIWSymbol (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) a (by linarith) E₀ (E j)) f x‖≤gs x) ∧
      ‖gs‖≤K₀*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
    cases E₀ with
    | none =>
      refine ⟨0,fun _ => le_rfl,?_,?_⟩
      · intro j x
        simp only [fixedPageOriginalSymbol,fixedPageIWSymbol,Option.elim_none,sub_self,
          integerMultiplier_zero,zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,le_refl]
      · simp only [norm_zero]
        positivity
    | some F =>
      obtain ⟨gs,hgs,hts,hns⟩ := iw_quantitative_model_comparison hC hCb HB hA.le hr hk hQ hM d hbudget
        (fun _ => F.beta) (fun _ => F.beta_pos.le) (fun _ => F.beta_lt_one.le)
        (rationalInducedSquareCoefficient F.conductor F.character)
        (fun t _ => (hGauss t).2 F.conductor F.character)
        (fun t _ => rationalInducedSquareCoefficient_norm_one F.conductor F.character t) R hR f
      refine ⟨gs,hgs,?_,hns⟩
      intro j x
      by_cases he : E j=some F
      · simpa only [fixedPageOriginalSymbol,fixedPageIWSymbol,Option.elim_some,ite_eq_left he] using hts j x
      · simpa only [fixedPageOriginalSymbol,fixedPageIWSymbol,Option.elim_some,ite_eq_right he,
          sub_self,integerMultiplier_zero,zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero] using hgs x
  obtain ⟨gs,hgs,hts,hns⟩ := hex
  let E' := fun j => largePageDatum (Q : ℝ) (E j)
  have hE' : ∀ j F,E' j=some F → PageConductorEligible c F := by
    intro j F hF
    have he := (largePageDatum_eq_some (Q : ℝ) (E j) F).mp hF
    exact page_source_region_eligible hc F (hE j F he.1).1 (hE j F he.1).2
  have hELarge : ∀ j F,E' j=some F → (Q : ℝ)<(F.conductor : ℝ) :=
    fun j F hF => ((largePageDatum_eq_some (Q : ℝ) (E j) F).mp hF).2
  obtain ⟨gl,hgl,htl,hnl⟩ := hLarge Q hQ0 M hM E' hE' hELarge R hR0 f
  refine ⟨go+gs+gl,fun x => add_nonneg (add_nonneg (hgo x) (hgs x)) (hgl x),?_,?_⟩
  · intro j x
    rw [page_model_IW_difference _ _ _ _ _ _ E₀ (E j)
      (fun F hF => (h₀ F hF).1) (hselected j),integerMultiplier_sub,integerMultiplier_sub,
      _root_.sub_apply,_root_.sub_apply,lp.coeFn_sub,lp.coeFn_sub,Pi.sub_apply,Pi.sub_apply]
    change _≤go x+gs x+gl x
    exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hto j x) (hts j x))) (htl j x))
  · have hn := (norm_add_le (go+gs) gl).trans
      (add_le_add ((norm_add_le go gs).trans (add_le_add hno hns)) hnl)
    exact hn.trans_eq (by ring)

end PrimeSquares
