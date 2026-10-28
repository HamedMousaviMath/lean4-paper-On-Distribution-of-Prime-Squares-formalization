import PrimeSquares.IWAnnularDenominatorTails
import PrimeSquares.ActualPageHighMaximum

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem iw_conductor_denominator_power {Q D q : ℝ}
    (hQ : 0<Q) (hD : 0<D) (hQD : Q≤D) (hDq : D≤q) :
    q^(-(3/8 : ℝ))≤Q^(-(1/4 : ℝ))*D^(-(1/16 : ℝ))*q^(-(1/16 : ℝ)) := by
  have hq : 0<q := hD.trans_le hDq
  have hs : q^(-(1/8 : ℝ))≤D^(-(1/16 : ℝ))*q^(-(1/16 : ℝ)) := by
    calc
      _ = q^(-(1/16 : ℝ))*q^(-(1/16 : ℝ)) := by rw [←Real.rpow_add hq];norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hD hDq (by norm_num)) (by positivity)
  exact (iw_denominator_tail_power hQ (hQD.trans hDq)).trans
    ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

noncomputable def pageExceptionalAnnularSymbol (N : ℕ) (hN : 1≤N)
    (R : ℝ) (E : Option PageZeroDatum) : C(PrimeCircle,ℂ) :=
  E.elim 0 (fun F => varyingIndexAnnularBlock
    ((sourceRationalCenters R).filter (fun r => F.conductor∣r.den)) N hN F.beta
    (fun r => rationalTwistedGauss r (sourceInducedCharacter F.conductor F.character r)))

theorem iw_large_conductor_maximum {C c : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) (hc : 0<c) (HPage : RawPageUniquenessInput c) :
    ∃ K : ℝ,0<K ∧ ∀ Q : ℝ,0<Q → ∀ (M : ℕ) (hM : 2≤M)
      (E : ℕ → Option PageZeroDatum),
      (∀ j F,E j=some F → PageConductorEligible c F) →
      (∀ j F,E j=some F → Q<(F.conductor : ℝ)) →
      ∀ (R : ℕ → ℝ),(∀ j,0≤R j) → ∀ f : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
        (∀ j x,‖integerMultiplier (pageExceptionalAnnularSymbol ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (R j) (E j)) f x‖≤g x) ∧
        ‖g‖≤K*Q^(-(1/4 : ℝ))*‖f‖ := by
  classical
  obtain ⟨A,hA,hGauss⟩ := rationalGauss_uniform_decay (by norm_num : (3/8 : ℝ)<1/2)
  let H := annularPowerConstant C (1/16)*A
  have hH : 0<H := mul_pos (annularPowerConstant_pos hC _) hA
  have hratio := (dyadic_decay_ratio (by norm_num : (0 : ℝ)<1/16)).2
  have hinv : 0<(1-(2 : ℝ)^(-(1/16 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  let K := H*(1-(2 : ℝ)^(-(1/16 : ℝ)))⁻¹
  refine ⟨K,mul_pos hH hinv,?_⟩
  intro Q hQ M hM E hE hLarge R hR f
  have hex (F : PageZeroDatum) : ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,Q<(F.conductor : ℝ) → ∀ x,‖integerMultiplier
        (varyingIndexAnnularBlock ((sourceRationalCenters (R j)).filter (fun r => F.conductor∣r.den))
          ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) F.beta
          (fun r => rationalTwistedGauss r (sourceInducedCharacter F.conductor F.character r))) f x‖≤g x) ∧
      ‖g‖≤H*Q^(-(1/4 : ℝ))*(F.conductor : ℝ)^(-(1/16 : ℝ))*‖f‖ := by
    by_cases hF : Q<(F.conductor : ℝ)
    · have hD : (0 : ℝ)<F.conductor := by exact_mod_cast (show 0<F.conductor by have h := F.conductor_two;omega)
      obtain ⟨g,hg,ht,hn⟩ := powerAnnular_countable_maximum hC HB (by norm_num : (0 : ℝ)<1/16)
        hM (fun r => F.conductor∣r.den) (fun _ => F.beta) (fun _ => F.beta_pos.le)
        (fun _ => F.beta_lt_one.le)
        (fun r => rationalTwistedGauss r (sourceInducedCharacter F.conductor F.character r))
        (show 0≤A*Q^(-(1/4 : ℝ))*(F.conductor : ℝ)^(-(1/16 : ℝ)) by positivity)
        (fun r _ hd => ((hGauss r).2 _).trans
          ((mul_le_mul_of_nonneg_left
            (iw_conductor_denominator_power hQ hD hF.le
              (by exact_mod_cast Nat.le_of_dvd r.den_pos hd)) hA.le).trans_eq (by ring))) R hR f
      refine ⟨g,hg,fun j _ x => ht j x,?_⟩
      convert hn using 1;dsimp [H];ring
    · refine ⟨0,fun _ => le_rfl,fun _ h => (hF h).elim,?_⟩
      simp only [norm_zero]
      positivity
  choose G hG0 hGt hGn using hex
  apply finite_family_countable_maximum
    (fun j => integerMultiplier (pageExceptionalAnnularSymbol ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (R j) (E j)) f)
    (by dsimp [K];positivity)
  intro J
  let S := J.biUnion (fun j => (E j).toFinset)
  have hS : ∀ F∈S,PageConductorEligible c F := by
    intro F hF
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hF
    exact hE j F (by simpa only [Option.mem_toFinset,Option.mem_def] using hj)
  let g := ∑ F∈S,G F
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0≤(∑ F∈S,G F) x
    simpa only [lp.coeFn_sum,Finset.sum_apply] using sum_nonneg (fun F _ => hG0 F x)
  · intro j hj x
    cases he : E j with
    | none =>
      simp only [pageExceptionalAnnularSymbol,Option.elim_none,integerMultiplier_zero,
        zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero]
      change 0≤(∑ F∈S,G F) x
      simpa only [lp.coeFn_sum,Finset.sum_apply] using sum_nonneg (fun F _ => hG0 F x)
    | some F =>
      have hFS : F∈S := mem_biUnion.mpr ⟨j,hj,by simp only [he,Option.toFinset_some,mem_singleton]⟩
      have ht := hGt F j (hLarge j F he) x
      have hs := single_le_sum (f := fun F => G F x) (fun F _ => hG0 F x) hFS
      have h := ht.trans hs
      simpa only [pageExceptionalAnnularSymbol,he,Option.elim_some,g,lp.coeFn_sum,Finset.sum_apply] using h
  · calc
      _ ≤ ∑ F∈S,‖G F‖ := norm_sum_le _ _
      _ ≤ ∑ F∈S,H*Q^(-(1/4 : ℝ))*(F.conductor : ℝ)^(-(1/16 : ℝ))*‖f‖ :=
        sum_le_sum (fun F _ => hGn F)
      _ = (H*Q^(-(1/4 : ℝ))*‖f‖)*∑ F∈S,(F.conductor : ℝ)^(-(1/16 : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro F _
        ring
      _ ≤ (H*Q^(-(1/4 : ℝ))*‖f‖)*(1-(2 : ℝ)^(-(1/16 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left (pageFinite_conductor_budget hc HPage (by norm_num) S hS) (by positivity)
      _ = _ := by dsimp [K];ring

end PrimeSquares
