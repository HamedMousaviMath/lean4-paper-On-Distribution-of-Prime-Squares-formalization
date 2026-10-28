import PrimeSquares.PowerDecayingAnnularMaximum
import PrimeSquares.ThresholdAnnularSource
import PrimeSquares.CompleteRationalCollarEnergy
import PrimeSquares.CollarConstantLinearity

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def thresholdPowerConstant (C η w : ℝ) : ℝ :=
  annularPowerConstant C η+collarPowerConstant 1 η*w^(-η)

theorem thresholdPowerConstant_pos {C η w : ℝ} (hC : 0 ≤ C) (hη : η<1) (hw : 0<w) :
    0<thresholdPowerConstant C η w := by
  have hA := annularPowerConstant_pos hC η
  have hB := collarPowerConstant_pos (by norm_num : (0 : ℝ)<1) hη
  unfold thresholdPowerConstant
  positivity

theorem powerThreshold_countable_maximum {C η w W : ℝ} (hC : 0 ≤ C)
    (hBourgain : SmoothCircleBourgainInput C) (hη0 : 0<η) (hη1 : η<1) (hw : 0<w) (hW : w ≤ W)
    {M : ℕ} (hM : 2 ≤ M) (P : ℚ → Prop) [DecidablePred P]
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0<A)
    (hc : ∀ r,r ∈ Set.Ico (0 : ℚ) 1 → P r → ‖c r‖ ≤ A*(r.den : ℝ)^(-η))
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock ((sourceRationalCenters (R j)).filter P)
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (thresholdPowerConstant C η w*A)*‖f‖ := by
  classical
  have hWp : 0<W := hw.trans_le hW
  have hColl := collarPowerConstant_pos (by norm_num : (0 : ℝ)<1) hη1
  let Γ := (sourceRationalCenters W).filter P
  let cc := fun j r => if (r.den : ℝ) ≤ R j then c r else 0
  let m := fun j => rationalCollarBlock Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) W (fun _ => β j) (cc j)
  let B := collarPowerConstant 1 η*w^(-η)*A
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 := fun r hr =>
    ((mem_sourceRationalCenters hWp.le r).mp (mem_filter.mp hr).1).1
  have hcap : ∀ r ∈ Γ,r.den ≤ ⌊W⌋₊ := fun r hr =>
    ((mem_canonicalRationalCenters _ _).mp (mem_filter.mp hr).1).2
  have hcc : ∀ j,∀ r ∈ Γ,‖cc j r‖ ≤ A*(r.den : ℝ)^(-η) := by
    intro j r hr
    dsimp [cc]
    split_ifs
    · exact hc r (hcan r hr) (mem_filter.mp hr).2
    · simp only [norm_zero]
      positivity
  have henergy (J : Finset ℕ) (θ : PrimeCircle) : (∑ j ∈ J,‖m j θ‖^2) ≤ B^2 := by
    by_cases hW1 : 1 ≤ W
    · have h := completeRationalCollar_finite_energy hM Γ hcan hW1 hA hη0.le hη1 hcap
        (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j) cc hcc J θ
      have hscale : collarPowerConstant A η*W^(-η) ≤ B := by
        have he : collarPowerConstant A η=collarPowerConstant 1 η*A := by
          simpa only [one_mul] using collarPowerConstant_mul 1 A η
        rw [he]
        have hp := Real.rpow_le_rpow_of_nonpos hw hW (neg_nonpos.mpr hη0.le)
        have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ collarPowerConstant 1 η*A by positivity)
        dsimp [B]
        convert h using 1;ring
      exact h.trans (pow_le_pow_left₀ (by have hp := collarPowerConstant_pos hA hη1;positivity) hscale 2)
    · have hf : ⌊W⌋₊=0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hW1)
      have hΓ : Γ=∅ := by simp only [Γ,sourceRationalCenters,hf,canonicalRationalCenters_zero,filter_empty]
      simpa only [m,hΓ,rationalCollarBlock,sum_empty,ContinuousMap.zero_apply,norm_zero,zero_pow (by norm_num : 2 ≠ 0),sum_const_zero]
        using sq_nonneg B
  obtain ⟨gC,_,hgC,htC,hnC⟩ := circle_energy_maximal_witness m hB henergy f
  obtain ⟨gL,hgL,htL,hnL⟩ := powerAnnular_countable_maximum hC hBourgain hη0 hM
    (fun r => P r ∧ W<(r.den : ℝ)) β hβ0 hβ1 c hA.le (fun r hr hp => hc r hr hp.1) R hR f
  have hsmallSet (j : ℕ) : ((sourceRationalCenters (R j)).filter P).filter (fun r => (r.den : ℝ) ≤ W)=
      Γ.filter (fun r => (r.den : ℝ) ≤ R j) := by
    ext r
    simp only [Γ,mem_filter,mem_sourceRationalCenters (hR j),mem_sourceRationalCenters hWp.le]
    tauto
  have hlargeSet (j : ℕ) : ((sourceRationalCenters (R j)).filter P).filter (fun r => W<(r.den : ℝ))=
      (sourceRationalCenters (R j)).filter (fun r => P r ∧ W<(r.den : ℝ)) := by
    ext r
    simp only [mem_filter,and_assoc]
  refine ⟨gC+gL,fun x => add_nonneg (hgC x) (hgL x),?_,?_⟩
  · intro j x
    rw [thresholdAnnularBlock_split,hsmallSet,hlargeSet,rationalCollarBlock_truncation,integerMultiplier_add,
      _root_.add_apply,lp.coeFn_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (htC j x) (htL j x))
  · exact (norm_add_le _ _).trans ((add_le_add hnC hnL).trans_eq (by
      unfold thresholdPowerConstant;dsimp [B];ring))

end PrimeSquares
