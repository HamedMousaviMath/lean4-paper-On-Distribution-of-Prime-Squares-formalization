import PrimeSquares.PowerThresholdUniformMaximum
import PrimeSquares.Proposition621Asymptotic
import PrimeSquares.ConductorGaussEnvelope

open Finset
open scoped lp
namespace PrimeSquares

theorem actualPageHigh_uniform_maximum {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) :
    ∃ D : ℝ,0<D ∧ ∀ Q : ℝ,2 ≤ Q → ∀ (M : ℕ) (hM : 2 ≤ M)
      (E : ℕ → Option PageZeroDatum),(∀ j F,E j=some F → PageConductorEligible c F) →
    ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) → ∀ f : ℓ²(ℤ,ℂ),
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖pageHighOperator ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega)
        Q (R j) (E j) f x‖ ≤ g x) ∧ ‖g‖ ≤ D*‖f‖ := by
  classical
  obtain ⟨Co,hCo,hGo⟩ := rationalGauss_uniform_decay (by norm_num : (1/4 : ℝ)<1/2)
  obtain ⟨Ce,hCe,hGe⟩ := conductorGauss_envelope (η := (1/4 : ℝ)) (ε := (1/8 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨T,hT,hMajorant⟩ := conductorMajorant_linear_bound
  let w : ℝ := 2/T
  have hw : 0<w := div_pos (by norm_num) hT
  let Ko := thresholdPowerConstant C (1/4) 2*Co
  let Ke := thresholdPowerConstant C (1/4) w*Ce
  have hKo : 0<Ko := mul_pos (thresholdPowerConstant_pos hC (by norm_num) (by norm_num)) hCo
  have hKe : 0<Ke := mul_pos (thresholdPowerConstant_pos hC (by norm_num) hw) hCe
  have hr := (dyadic_decay_ratio (by norm_num : (0 : ℝ)<1/8)).2
  have hinv : 0<(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  let D := 1+Ko+Ke*(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹
  refine ⟨D,by dsimp [D];positivity,?_⟩
  intro Q hQ M hM E hE R hR f
  have hQp : 0<Q := by linarith
  let β := fun j => optionPageBeta (E j)
  have hβ0 : ∀ j,0 ≤ β j := fun j => optionPageBeta_nonneg (E j)
  have hβ1 : ∀ j,β j ≤ 1 := fun j => optionPageBeta_le_one (E j)
  obtain ⟨go,hgo,hto,hno⟩ := powerThreshold_countable_maximum hC hBourgain
    (by norm_num : (0 : ℝ)<1/4) (by norm_num : (1/4 : ℝ)<1) (by norm_num : (0 : ℝ)<2) hQ hM
    (fun _ => True) (fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)
    rationalPrincipalGauss hCo (fun r _ _ => (hGo r).1) R hR f
  simp only [filter_true] at hto
  have hno' : ‖go‖ ≤ Ko*‖f‖ := hno
  have hex (F : PageZeroDatum) := by
    have hq : 0<F.conductor := by have h := F.conductor_two;omega
    have hqr : (0 : ℝ)<F.conductor := by exact_mod_cast hq
    have hB : 0<conductorMajorant F.conductor := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le _ hq)
    have hW : w ≤ Q*(F.conductor : ℝ)/conductorMajorant F.conductor := by
      dsimp [w]
      apply (div_le_div_iff₀ hT hB).mpr
      have h := hMajorant F.conductor hq
      nlinarith
    exact powerThreshold_countable_maximum hC hBourgain
      (by norm_num : (0 : ℝ)<1/4) (by norm_num : (1/4 : ℝ)<1) hw hW hM
      (fun r => F.conductor ∣ r.den) β hβ0 hβ1
      (fun r => rationalTwistedGauss r (sourceInducedCharacter F.conductor F.character r))
      (mul_pos hCe (Real.rpow_pos_of_pos hqr (-(1/8 : ℝ))))
      (fun r _ hd => hGe F.conductor hq r hd (sourceInducedCharacter F.conductor F.character r)) R hR f
  choose G hG0 hGt hGn using hex
  have hGn' (F : PageZeroDatum) : ‖G F‖ ≤ (Ke*(F.conductor : ℝ)^(-(1/8 : ℝ)))*‖f‖ :=
    (hGn F).trans_eq (by dsimp [Ke];ring)
  have hD : 0 ≤ D := by dsimp [D];positivity
  apply finite_family_countable_maximum
    (fun j => pageHighOperator ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) Q (R j) (E j) f)
    (by positivity)
  intro J
  let S := J.biUnion (fun j => (E j).toFinset)
  have helig : ∀ F ∈ S,PageConductorEligible c F := by
    intro F hF
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hF
    exact hE j F (by simpa only [Option.mem_toFinset,Option.mem_def] using hj)
  let g := go+∑ F ∈ S,G F
  have hnSum : (∑ F ∈ S,‖G F‖) ≤ (Ke*‖f‖)*(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ F ∈ S,(Ke*(F.conductor : ℝ)^(-(1/8 : ℝ)))*‖f‖ := sum_le_sum (fun F _ => hGn' F)
      _ = (Ke*‖f‖)*∑ F ∈ S,(F.conductor : ℝ)^(-(1/8 : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro F _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pageFinite_conductor_budget hc hPage (by norm_num : (0 : ℝ)<1/8) S helig) (by positivity)
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0 ≤ (go+∑ F ∈ S,G F) x
    simpa only [lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using
      add_nonneg (hgo x) (sum_nonneg (fun F _ => hG0 F x))
  · intro j hj x
    cases he : E j with
    | none =>
      rw [pageHighOperator_none _ _ hQp]
      have hh := (hto j x).trans (le_add_of_nonneg_right (sum_nonneg (fun F _ => hG0 F x) : 0 ≤ ∑ F ∈ S,G F x))
      simpa only [g,lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using hh
    | some F =>
      have hFS : F ∈ S := mem_biUnion.mpr ⟨j,hj,by simp only [he,Option.toFinset_some,mem_singleton]⟩
      rw [pageHighOperator_some _ _ hQp,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]
      have hF := hGt F j x
      simp only [β,he,optionPageBeta_some] at hF
      have hh := (norm_sub_le _ _).trans (add_le_add (hto j x) hF)
      have hs := single_le_sum (fun F _ => hG0 F x) hFS
      have hh' := hh.trans (add_le_add (le_refl (go x)) hs)
      simpa only [g,lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using hh'
  · have hconst : Ko+Ke*(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹ ≤ D := by dsimp [D];linarith
    calc
      _ ≤ ‖go‖+‖∑ F ∈ S,G F‖ := norm_add_le _ _
      _ ≤ Ko*‖f‖+∑ F ∈ S,‖G F‖ := add_le_add hno' (norm_sum_le _ _)
      _ ≤ Ko*‖f‖+(Ke*‖f‖)*(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹ := add_le_add (le_refl _) hnSum
      _ = (Ko+Ke*(1-(2 : ℝ)^(-(1/8 : ℝ)))⁻¹)*‖f‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (norm_nonneg f)

theorem sourcePageDyadicTail_uniform {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) :
    ∃ D : ℝ,0<D ∧ ∀ Q : ℝ,2 ≤ Q → ∀ N₀ : ℝ,2 ≤ N₀ →
    ∀ E : ℕ → Option PageZeroDatum,
      (∀ j F,N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → E j=some F →
        (F.conductor : ℝ) ≤ sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q ∧
        1-(c/2)/Real.log (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)<F.beta) →
    ∀ f : ℓ²(ℤ,ℂ),∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,G x=⨆ j : ℕ,‖sourcePageDyadicTailOperator N₀ Q E j f x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ G x) ∧ ‖G‖ ≤ D*‖f‖ := by
  classical
  obtain ⟨D,hD,hmax⟩ := actualPageHigh_uniform_maximum hC hBourgain hc hPage
  refine ⟨D,hD,?_⟩
  intro Q hQ N₀ _ E hE f
  let E' := fun j => if N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) then E j else none
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q
  have hE' : ∀ j F,E' j=some F → PageConductorEligible c F := by
    intro j F hj
    by_cases hvalid : N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ)
    · have hF : E j=some F := by simpa only [E',ite_eq_left hvalid] using hj
      exact page_source_region_eligible hc F (hE j F hvalid hF).1 (hE j F hvalid hF).2
    · simp only [E',ite_eq_right hvalid] at hj
      cases hj
  obtain ⟨g,hg,ht,hn⟩ := hmax Q hQ 2 (by norm_num) E' hE' R (fun j => (sourceMajorArcScale_pos _ _).le) f
  have hdom : ∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ g x := by
    intro j x
    by_cases hvalid : N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ)
    · simpa only [sourcePageDyadicTailOperator,ite_eq_left hvalid,E',R] using ht j x
    · simpa only [sourcePageDyadicTailOperator,ite_eq_right hvalid,zero_apply,lp.coeFn_zero,
        Pi.zero_apply,norm_zero] using hg x
  obtain ⟨G,hGeq,hG0,hGt,hGn⟩ := exact_maximum_of_majorant
    (fun j => sourcePageDyadicTailOperator N₀ Q E j f) g hg hdom
  exact ⟨G,hGeq,hG0,hGt,hGn.trans hn⟩

end PrimeSquares
