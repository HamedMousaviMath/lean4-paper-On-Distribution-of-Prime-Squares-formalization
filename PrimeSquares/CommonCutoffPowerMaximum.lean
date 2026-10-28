import PrimeSquares.CommonCutoffAnnularMaximum
import PrimeSquares.IWAnnularDenominatorTails

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem common_cutoff_power_maximum {C A a η : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) (hA : 0≤A) (ha : 4≤a) (hη : 0<η)
    {M K : ℕ} (hM : 2≤M) (Γ : Finset ℚ)
    (hcan : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1) (hcap : ∀ r∈Γ,r.den≤K)
    (hsmall : ∀ r∈Γ,4≤r.den)
    (hwide : ∀ r∈Γ,2*(16 : ℝ)^(Nat.log2 r.den)≤a)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ r∈Γ,‖c r‖≤A*(r.den : ℝ)^(-η)) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (weightedWidthAnnularBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a (by linarith) c) f x‖≤g x) ∧
      ‖g‖≤(annularPowerConstant C η*A)*‖f‖ := by
  classical
  have hcoef (s : ℕ) (r : ℚ) (hr : r∈Γ.filter (fun r => Nat.log2 r.den=s)) :
      ‖c r‖≤A*((2 : ℝ)^s)^(-η) := by
    have hmem := mem_filter.mp hr
    have hb := sourceDyadicRationalCenters_den_bounds
      ((mem_sourceDyadicRationalCenters _ _).mpr ⟨hcan r hmem.1,hmem.2⟩)
    exact (hc r hmem.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hb.1 (neg_nonpos.mpr hη.le)) hA)
  have hex (s : ℕ) : ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (weightedWidthAnnularBlock (Γ.filter (fun r => Nat.log2 r.den=s))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega)
        (β j) a (by linarith) c) f x‖≤g x) ∧
      ‖g‖≤(allIndexAnnularConstant C*(A*((2 : ℝ)^s)^(-η))*((s : ℝ)+1)^3)*‖f‖ := by
    by_cases he : (Γ.filter (fun r => Nat.log2 r.den=s)).Nonempty
    · obtain ⟨r,hr⟩ := he
      have hmem := mem_filter.mp hr
      have hb := sourceDyadicRationalCenters_den_bounds
        ((mem_sourceDyadicRationalCenters _ _).mpr ⟨hcan r hmem.1,hmem.2⟩)
      have hs : 2≤s := by
        by_contra hs
        have hp : (2 : ℝ)^(s+1)≤4 :=
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega : s+1≤2)).trans_eq (by norm_num)
        have hlow : (4 : ℝ)≤r.den := by exact_mod_cast hsmall r hmem.1
        linarith
      have hw : 2*(16 : ℝ)^s≤a := by simpa only [hmem.2] using hwide r hmem.1
      exact common_cutoff_band_maximum hC HB (by positivity) ha hM hs hw
        (Γ.filter (fun r => Nat.log2 r.den=s))
        (fun r hr => hcan r (mem_filter.mp hr).1)
        (fun r hr => (sourceDyadicRationalCenters_den_bounds ((mem_sourceDyadicRationalCenters _ _).mpr
          ⟨hcan r (mem_filter.mp hr).1,(mem_filter.mp hr).2⟩)).2.le)
        β hβ0 hβ1 c (hcoef s) f
    · have hzero : Γ.filter (fun r => Nat.log2 r.den=s)=∅ := not_nonempty_iff_eq_empty.mp he
      refine ⟨0,fun _ => le_rfl,?_,?_⟩
      · intro j x
        simp only [hzero,weightedWidthAnnularBlock,sum_empty,integerMultiplier_zero,
          zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,le_refl]
      · have hK := allIndexAnnularConstant_pos hC
        simp only [norm_zero]
        positivity
  choose G hG0 hGt hGn using hex
  let S := range (Nat.log2 K+1)
  let g := ∑ s∈S,G s
  have heq (j : ℕ) : weightedWidthAnnularBlock Γ ((2 : ℕ)^j*M)
      (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a (by linarith) c=
      ∑ s∈S,weightedWidthAnnularBlock (Γ.filter (fun r => Nat.log2 r.den=s)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a (by linarith) c := by
    unfold weightedWidthAnnularBlock
    exact rational_dyadic_partition Γ K hcap _
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hη
  have hsum := shifted_polynomial_geometric_summable 3 hr0 hr1
  have hKb : allIndexAnnularConstant C*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s)≤
      annularPowerConstant C η := by unfold annularPowerConstant;linarith
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0≤(∑ s∈S,G s) x
    simpa only [lp.coeFn_sum,Finset.sum_apply] using sum_nonneg (fun s _ => hG0 s x)
  · intro j x
    change _≤(∑ s∈S,G s) x
    rw [heq,integerMultiplier_finset_sum,_root_.sum_apply]
    simp only [lp.coeFn_sum,Finset.sum_apply]
    exact (norm_sum_le _ _).trans (sum_le_sum (fun s _ => hGt s j x))
  · calc
      _ ≤ ∑ s∈S,‖G s‖ := norm_sum_le _ _
      _ ≤ ∑ s∈S,(allIndexAnnularConstant C*(A*((2 : ℝ)^s)^(-η))*((s : ℝ)+1)^3)*‖f‖ :=
        sum_le_sum (fun s _ => hGn s)
      _ = (allIndexAnnularConstant C*A*‖f‖)*∑ s∈S,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s := by
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        rw [dyadic_pow_rpow]
        ring
      _ ≤ (allIndexAnnularConstant C*A*‖f‖)*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s) := by
        apply mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun s _ => by positivity))
        have hK := allIndexAnnularConstant_pos hC
        positivity
      _ = (allIndexAnnularConstant C*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s))*A*‖f‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKb hA) (norm_nonneg f)

theorem common_cutoff_denominator_tail {C A a Q : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) (hA : 0≤A) (ha : 4≤a) (hQ : 4≤Q)
    {M K : ℕ} (hM : 2≤M) (Γ : Finset ℚ)
    (hcan : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1) (hcap : ∀ r∈Γ,r.den≤K)
    (hwide : ∀ r∈Γ,2*(16 : ℝ)^(Nat.log2 r.den)≤a)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ r∈Γ,‖c r‖≤A*(r.den : ℝ)^(-(3/8 : ℝ))) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (weightedWidthAnnularBlock (Γ.filter (fun r => Q<(r.den : ℝ)))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega)
        (β j) a (by linarith) c) f x‖≤g x) ∧
      ‖g‖≤(annularPowerConstant C (1/8)*A*Q^(-(1/4 : ℝ)))*‖f‖ := by
  classical
  have hQ0 : 0<Q := by linarith
  obtain ⟨g,hg,ht,hn⟩ := common_cutoff_power_maximum hC HB
    (show 0≤A*Q^(-(1/4 : ℝ)) by positivity) ha (by norm_num : (0 : ℝ)<1/8) hM
    (Γ.filter (fun r => Q<(r.den : ℝ)))
    (fun r hr => hcan r (mem_filter.mp hr).1) (fun r hr => hcap r (mem_filter.mp hr).1)
    (fun r hr => by exact_mod_cast hQ.trans (mem_filter.mp hr).2.le)
    (fun r hr => hwide r (mem_filter.mp hr).1) β hβ0 hβ1 c
    (fun r hr => (hc r (mem_filter.mp hr).1).trans
      ((mul_le_mul_of_nonneg_left (iw_denominator_tail_power hQ0 (mem_filter.mp hr).2.le) hA).trans_eq (by ring))) f
  refine ⟨g,hg,ht,?_⟩
  convert hn using 1;ring

end PrimeSquares
