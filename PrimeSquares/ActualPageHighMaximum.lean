import PrimeSquares.SharpChangingCharacterMaximum
import PrimeSquares.PageConductorClassSelection

open scoped lp
namespace PrimeSquares

theorem optionPageConductor_some (k : ℕ) (F : PageZeroDatum) : optionPageConductor k (some F)=F.conductor := rfl
theorem optionPageConductor_none (k : ℕ) : optionPageConductor k none=k := rfl
theorem optionPageBeta_some (F : PageZeroDatum) : optionPageBeta (some F)=F.beta := rfl
theorem optionPageBeta_none : optionPageBeta none=1 := rfl

noncomputable def pageHighOperator (N : ℕ) (hN : 1 ≤ N) (Q R : ℝ) (E : Option PageZeroDatum) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  circleHighOperator (sourceRationalCenters R) N hN (optionPageConductor 1 E) Q
    (conductorMajorant (optionPageConductor 1 E))
    (sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E))
    (sourceExceptionalSelector (optionPageConductor 1 E) E.isSome) (optionPageBeta E)

theorem circleHighOperator_inactive (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (hq : 0<q)
    {Q B : ℝ} (hQ : 0<Q) (hB : 0<B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighOperator Γ N hN q Q B χ (sourceExceptionalSelector q false) β=
      integerMultiplier (thresholdAnnularBlock Γ N hN 1 Q rationalPrincipalGauss) := by
  unfold circleHighOperator
  rw [circleHighModel_threshold_decomposition Γ N hN hq hQ hB,thresholdAnnularBlock_mask]
  simp only [Bool.false_eq_true,ite_false,sub_zero]

theorem pageHighOperator_none (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0<Q) (R : ℝ) :
    pageHighOperator N hN Q R none=integerMultiplier
      (thresholdAnnularBlock (sourceRationalCenters R) N hN 1 Q rationalPrincipalGauss) := by
  unfold pageHighOperator
  exact circleHighOperator_inactive _ _ _ 1 (by norm_num) hQ
    (lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le 1 (by norm_num))) _ _

theorem pageHighOperator_some (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0<Q) (R : ℝ) (F : PageZeroDatum) :
    pageHighOperator N hN Q R (some F)=
      integerMultiplier (thresholdAnnularBlock (sourceRationalCenters R) N hN 1 Q rationalPrincipalGauss)-
      integerMultiplier (thresholdAnnularBlock ((sourceRationalCenters R).filter (fun r => F.conductor ∣ r.den))
        N hN F.beta (Q*(F.conductor : ℝ)/conductorMajorant F.conductor)
        (fun r => rationalTwistedGauss r (sourceInducedCharacter F.conductor F.character r))) := by
  have hq : 0<F.conductor := by have h := F.conductor_two;omega
  unfold pageHighOperator circleHighOperator
  change integerMultiplier (circleHighModel _ _ _ F.conductor Q (conductorMajorant F.conductor)
    (sourceInducedCharacter F.conductor F.character) (sourceExceptionalSelector F.conductor true) F.beta)=_
  rw [circleHighModel_threshold_decomposition _ _ _ hq hQ
    (lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le _ hq)),thresholdAnnularBlock_mask]
  simp only [ite_true]
  exact integerMultiplier_sub _ _

theorem pageFinite_conductor_budget {c ε : ℝ} (hc : 0<c) (hPage : RawPageUniquenessInput c)
    (hε : 0<ε) (S : Finset PageZeroDatum) (hS : ∀ F ∈ S,PageConductorEligible c F) :
    (∑ F ∈ S,(F.conductor : ℝ)^(-ε)) ≤ (1-(2 : ℝ)^(-ε))⁻¹ := by
  classical
  have hinj : ∀ F ∈ S,∀ G ∈ S,Nat.log2 F.conductor=Nat.log2 G.conductor → F=G := by
    intro F hF G hG hb
    exact page_dyadic_uniqueness hc hPage F G (hS F hF) (hS G hG) hb
  have hterm (F : PageZeroDatum) : (F.conductor : ℝ)^(-ε) ≤ ((2 : ℝ)^(-ε))^(Nat.log2 F.conductor) := by
    have hq : F.conductor ≠ 0 := by have h := F.conductor_two;omega
    have hlo := ((Nat.log2_eq_iff hq).mp (show Nat.log2 F.conductor=Nat.log2 F.conductor from rfl)).1
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ)<(2 : ℝ)^(Nat.log2 F.conductor))
      (by exact_mod_cast hlo : (2 : ℝ)^(Nat.log2 F.conductor) ≤ F.conductor) (neg_nonpos.mpr hε.le)
    simpa only [dyadic_pow_rpow] using h
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hε
  calc
    _ ≤ ∑ F ∈ S,((2 : ℝ)^(-ε))^(Nat.log2 F.conductor) := Finset.sum_le_sum (fun F _ => hterm F)
    _ = ∑ i ∈ S.image (fun F => Nat.log2 F.conductor),((2 : ℝ)^(-ε))^i := by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ ∑' i : ℕ,((2 : ℝ)^(-ε))^i :=
      (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum _ (fun i _ => pow_nonneg hr0.le i)
    _ = _ := tsum_geometric_of_lt_one hr0.le hr1

theorem actualPageHigh_maximum {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) :
    ∃ Q₀ D : ℝ,16 ≤ Q₀ ∧ 0<D ∧ ∀ Q : ℝ,Q₀ ≤ Q → 2 ≤ Real.log Q →
    gaussThresholdSlope (Real.log Q) ≤ 1/4 → ∀ (M : ℕ) (hM : 2 ≤ M)
      (E : ℕ → Option PageZeroDatum),(∀ j F,E j=some F → PageConductorEligible c F) →
    ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) → ∀ f : ℓ²(ℤ,ℂ),
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖pageHighOperator ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega)
        Q (R j) (E j) f x‖ ≤ g x) ∧ ‖g‖ ≤ (D*sharpHighMaximalRate Q)*‖f‖ := by
  classical
  obtain ⟨Q₀,H,hQ₀,hH,hExc⟩ := sharpExceptional_conductor_rate hC hBourgain
  have hK := sharpThresholdMaximalConstant_nonneg hC
  have hratio := (dyadic_decay_ratio (by norm_num : (0 : ℝ)<1/50)).2
  have hinv : 0<(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  let D := 1+4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹
  refine ⟨Q₀,D,hQ₀,by dsimp [D];positivity,?_⟩
  intro Q hQ hL hSlope M hM E hE R hR f
  have hQ16 : 16 ≤ Q := hQ₀.trans hQ
  have hQ1 : 1 ≤ Q := by linarith
  have hQp : 0<Q := by linarith
  have hRate := sharpHighMaximalRate_nonneg hQ1
  let β := fun j => optionPageBeta (E j)
  have hβ0 : ∀ j,0 ≤ β j := fun j => optionPageBeta_nonneg (E j)
  have hβ1 : ∀ j,β j ≤ 1 := fun j => optionPageBeta_le_one (E j)
  obtain ⟨gO,hgO,htO,hnO⟩ := sharpOrdinary_rate_maximum hC hBourgain hM hQ16 hL hSlope R hR f
  have hex (F : PageZeroDatum) := by
    have : NeZero F.conductor := ⟨by have h := F.conductor_two;omega⟩
    exact hExc Q hQ hL hSlope M hM F.conductor F.character F.quadratic β hβ0 hβ1 R hR f
  choose G hG0 hGt hGn using hex
  have hD0 : 0 ≤ D := by dsimp [D];positivity
  apply finite_family_countable_maximum
    (fun j => pageHighOperator ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) Q (R j) (E j) f)
    (by positivity)
  intro J
  let S := J.biUnion (fun j => (E j).toFinset)
  have hS (F : PageZeroDatum) (hF : F ∈ S) : ∃ j,E j=some F := by
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hF
    exact ⟨j,by simpa only [Option.mem_toFinset,Option.mem_def] using hj⟩
  have helig : ∀ F ∈ S,PageConductorEligible c F := by
    intro F hF
    obtain ⟨j,hj⟩ := hS F hF
    exact hE j F hj
  let g := gO+∑ F ∈ S,G F
  have hnSum : (∑ F ∈ S,‖G F‖) ≤
      (H*sharpHighMaximalRate Q*‖f‖)*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ F ∈ S,(H*(F.conductor : ℝ)^(-(1/50 : ℝ))*sharpHighMaximalRate Q)*‖f‖ := Finset.sum_le_sum (fun F _ => hGn F)
      _ = (H*sharpHighMaximalRate Q*‖f‖)*∑ F ∈ S,(F.conductor : ℝ)^(-(1/50 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro F _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pageFinite_conductor_budget hc hPage (by norm_num : (0 : ℝ)<1/50) S helig) (by positivity)
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0 ≤ (gO+∑ F ∈ S,G F) x
    simpa only [lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using
      add_nonneg (hgO x) (Finset.sum_nonneg (fun F _ => hG0 F x))
  · intro j hj x
    cases he : E j with
    | none =>
      rw [pageHighOperator_none _ _ hQp]
      have hsum : 0 ≤ ∑ F ∈ S,G F x := Finset.sum_nonneg (fun F _ => hG0 F x)
      have hh := (htO j x).trans (le_add_of_nonneg_right hsum)
      simpa only [g,lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using hh
    | some F =>
      have hFS : F ∈ S := Finset.mem_biUnion.mpr ⟨j,hj,by simp only [he,Option.toFinset_some,Finset.mem_singleton]⟩
      rw [pageHighOperator_some _ _ hQp,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]
      have hF := hGt F j x
      simp only [β,he,optionPageBeta_some] at hF
      have hh := (norm_sub_le _ _).trans (add_le_add (htO j x) hF)
      have hs := Finset.single_le_sum (fun F _ => hG0 F x) hFS
      have hh' := hh.trans (add_le_add (le_refl (gO x)) hs)
      simpa only [g,lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using hh'
  · have hb : 4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ ≤ D := by dsimp [D];linarith
    calc
      _ ≤ ‖gO‖+‖∑ F ∈ S,G F‖ := norm_add_le _ _
      _ ≤ (4*sharpThresholdMaximalConstant C*sharpHighMaximalRate Q)*‖f‖+∑ F ∈ S,‖G F‖ :=
        add_le_add hnO (norm_sum_le _ _)
      _ ≤ (4*sharpThresholdMaximalConstant C*sharpHighMaximalRate Q)*‖f‖+
          (H*sharpHighMaximalRate Q*‖f‖)*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := add_le_add (le_refl _) hnSum
      _ = ((4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹)*sharpHighMaximalRate Q)*‖f‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hRate) (norm_nonneg f)

end PrimeSquares

