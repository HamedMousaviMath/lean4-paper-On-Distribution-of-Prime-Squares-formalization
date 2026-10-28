import PrimeSquares.SharpAnnularBlockMaximum
import PrimeSquares.PolynomialDyadicProfileSum
import PrimeSquares.DyadicDenominatorPartition

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def sharpThresholdBlockConstant (C : ℝ) : ℝ :=
  192/Real.pi+annularTruncationConstant C*(2 : ℝ)^(1/4 : ℝ)

noncomputable def sharpThresholdMaximalConstant (C : ℝ) : ℝ :=
  sharpThresholdBlockConstant C*polynomialDyadicProfileConstant (1/4) 3

theorem sharpThresholdBlockConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ sharpThresholdBlockConstant C := by
  have h := annularTruncationConstant_nonneg hC
  unfold sharpThresholdBlockConstant
  positivity

theorem sharpThresholdMaximalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ sharpThresholdMaximalConstant C := mul_nonneg (sharpThresholdBlockConstant_nonneg hC)
      (polynomialDyadicProfileConstant_nonneg (by norm_num : (0 : ℝ)<1/4) 3)

theorem sharpThreshold_block_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {A B Q W : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hW : 16 ≤ W)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (d : ℚ → ℕ) (hd : ∀ r ∈ Γ,0<d r)
    (hscale : ∀ r ∈ Γ,(r.den : ℝ)/W=(d r : ℝ)*B/Q) (c : ℚ → ℂ)
    (hc : ∀ r ∈ Γ,‖c r‖ ≤ A*(d r : ℝ)^(-(1/2 : ℝ))*conductorRho (d r))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (sharpThresholdBlockConstant C*sharpThresholdAmplitude A B Q*
        ((s : ℝ)+1)^3*relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := by
  classical
  let ΓS := Γ.filter (fun r => (r.den : ℝ) ≤ W)
  let ΓL := Γ.filter (fun r => W<(r.den : ℝ))
  obtain ⟨gS,hgS,htS,hnS⟩ := sharpCollar_block_maximum hM ΓS
    (fun r hr => hcan r (mem_filter.mp hr).1) (fun r hr => hlog r (mem_filter.mp hr).1)
    hA hB hQ (by linarith : 0<W) hL d (fun r hr => hd r (mem_filter.mp hr).1)
    (fun r hr => hscale r (mem_filter.mp hr).1) (fun r hr => (mem_filter.mp hr).2)
    c (fun r hr => hc r (mem_filter.mp hr).1) β hβ0 hβ1 R f
  obtain ⟨gL,hgL,htL,hnL⟩ := sharpLarge_block_maximum hC hBourgain hM ΓL
    (fun r hr => hcan r (mem_filter.mp hr).1) (fun r hr => hlog r (mem_filter.mp hr).1)
    hA hB hQ hW hL hSlope d (fun r hr => hd r (mem_filter.mp hr).1)
    (fun r hr => hscale r (mem_filter.mp hr).1) (fun r hr => (mem_filter.mp hr).2)
    c (fun r hr => hc r (mem_filter.mp hr).1) β hβ0 hβ1 R hR f
  have heq (j : ℕ) : thresholdAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
      ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c=
      rationalCollarBlock (ΓS.filter (fun r => (r.den : ℝ) ≤ R j)) ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) W (fun _ => β j) c+
      weightedAnnularSourceBlock (ΓL.filter (fun r => (r.den : ℝ) ≤ R j)) ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c := by
    rw [thresholdAnnularBlock_split]
    have hs : (Γ.filter (fun r => (r.den : ℝ) ≤ R j)).filter (fun r => (r.den : ℝ) ≤ W)=
        ΓS.filter (fun r => (r.den : ℝ) ≤ R j) := by ext r;simp only [ΓS,mem_filter,and_assoc,and_left_comm,and_comm]
    have hl : (Γ.filter (fun r => (r.den : ℝ) ≤ R j)).filter (fun r => W<(r.den : ℝ))=
        ΓL.filter (fun r => (r.den : ℝ) ≤ R j) := by ext r;simp only [ΓL,mem_filter,and_assoc,and_left_comm,and_comm]
    rw [hs,hl]
    congr 1
    apply sum_congr rfl
    intro r hr
    rw [hlog r (mem_filter.mp (mem_filter.mp hr).1).1]
  refine ⟨gS+gL,fun x => add_nonneg (hgS x) (hgL x),?_,?_⟩
  · intro j x
    rw [heq,integerMultiplier_add,_root_.add_apply,lp.coeFn_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (htS j x) (htL j x))
  · have hD := sharpThresholdAmplitude_nonneg hA (by linarith : (0 : ℝ) ≤ B) hQ.le
    have hprof := relativeCutoffProfile_nonneg (δ := (1/4 : ℝ)) (show 0 ≤ (2 : ℝ)^s/W by positivity)
    have hp : (1 : ℝ) ≤ ((s : ℝ)+1)^3 := one_le_pow₀ (by have h := Nat.cast_nonneg (α := ℝ) s;linarith)
    have hS : ((192/Real.pi)*sharpThresholdAmplitude A B Q*
        relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ ≤
        ((192/Real.pi)*sharpThresholdAmplitude A B Q*((s : ℝ)+1)^3*
        relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := by
      have hn : 0 ≤ ((192/Real.pi)*sharpThresholdAmplitude A B Q*
          relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := by positivity
      have hh := le_mul_of_one_le_right hn hp
      convert hh using 1;ring
    exact (norm_add_le _ _).trans ((add_le_add (hnS.trans hS) hnL).trans_eq (by
      unfold sharpThresholdBlockConstant;ring))

theorem sharpThreshold_finiteCenters_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M K : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hcap : ∀ r ∈ Γ,r.den ≤ K)
    {A B Q W : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hW : 16 ≤ W)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (d : ℚ → ℕ) (hd : ∀ r ∈ Γ,0<d r)
    (hscale : ∀ r ∈ Γ,(r.den : ℝ)/W=(d r : ℝ)*B/Q) (c : ℚ → ℂ)
    (hc : ∀ r ∈ Γ,‖c r‖ ≤ A*(d r : ℝ)^(-(1/2 : ℝ))*conductorRho (d r))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (sharpThresholdMaximalConstant C*sharpThresholdAmplitude A B Q*(1+Real.log W)^3)*‖f‖ := by
  classical
  have hex (s : ℕ) := sharpThreshold_block_maximum hC hBourgain hM (Γ.filter (fun r => Nat.log2 r.den=s))
    (fun r hr => hcan r (mem_filter.mp hr).1) (fun r hr => (mem_filter.mp hr).2)
    hA hB hQ hW hL hSlope d (fun r hr => hd r (mem_filter.mp hr).1)
    (fun r hr => hscale r (mem_filter.mp hr).1) c (fun r hr => hc r (mem_filter.mp hr).1) β hβ0 hβ1 R hR f
  choose G hG0 hGt hGn using hex
  let S := range (Nat.log2 K+1)
  let g := ∑ s ∈ S,G s
  have heq (j : ℕ) : thresholdAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
      ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c=
      ∑ s ∈ S,thresholdAnnularBlock ((Γ.filter (fun r => Nat.log2 r.den=s)).filter
        (fun r => (r.den : ℝ) ≤ R j)) ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) W c := by
    unfold thresholdAnnularBlock
    rw [rational_dyadic_partition _ K (fun r hr => hcap r (mem_filter.mp hr).1)]
    apply sum_congr rfl
    intro s _
    congr 1
    ext r
    simp only [mem_filter,and_assoc,and_left_comm,and_comm]
  have hD := sharpThresholdAmplitude_nonneg hA (by linarith : (0 : ℝ) ≤ B) hQ.le
  have hK0 := sharpThresholdBlockConstant_nonneg hC
  have hsum := polynomial_dyadic_profile_summable (by norm_num : (0 : ℝ)<1/4) (by linarith : 0<W) 3
  have htotal := polynomial_dyadic_profile_tsum (by norm_num : (0 : ℝ)<1/4) (show 1 ≤ W by linarith) 3
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0 ≤ (∑ s ∈ S,G s) x
    simpa only [lp.coeFn_sum,Finset.sum_apply] using sum_nonneg (fun s _ => hG0 s x)
  · intro j x
    change _ ≤ (∑ s ∈ S,G s) x
    rw [heq,integerMultiplier_finset_sum,_root_.sum_apply]
    simp only [lp.coeFn_sum,Finset.sum_apply]
    exact (norm_sum_le _ _).trans (sum_le_sum (fun s _ => hGt s j x))
  · calc
      _ ≤ ∑ s ∈ S,‖G s‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ S,(sharpThresholdBlockConstant C*sharpThresholdAmplitude A B Q*
          ((s : ℝ)+1)^3*relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := sum_le_sum (fun s _ => hGn s)
      _ = (sharpThresholdBlockConstant C*sharpThresholdAmplitude A B Q*‖f‖)*
          ∑ s ∈ S,((s : ℝ)+1)^3*relativeCutoffProfile (1/4) ((2 : ℝ)^s/W) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        ring
      _ ≤ (sharpThresholdBlockConstant C*sharpThresholdAmplitude A B Q*‖f‖)*
          (polynomialDyadicProfileConstant (1/4) 3*(1+Real.log W)^3) :=
        mul_le_mul_of_nonneg_left ((hsum.sum_le_tsum S (fun s _ => mul_nonneg (by positivity)
          (relativeCutoffProfile_nonneg (by positivity)))).trans htotal) (by positivity)
      _ = _ := by unfold sharpThresholdMaximalConstant;ring

end PrimeSquares
