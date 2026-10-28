import PrimeSquares.AllIndexAnnularTruncationMaximum
import PrimeSquares.PolynomialDyadicProfileSum
import PrimeSquares.DyadicDenominatorPartition
import PrimeSquares.FiniteFamilyCountableCriterion

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def varyingIndexAnnularBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,c r • circleAnnularSource N hN β (Nat.log2 r.den) r

noncomputable def annularPowerConstant (C η : ℝ) : ℝ :=
  1+allIndexAnnularConstant C*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s)

theorem annularPowerConstant_pos {C : ℝ} (hC : 0 ≤ C) (η : ℝ) : 0<annularPowerConstant C η := by
  have hK := allIndexAnnularConstant_pos hC
  have hsum : 0 ≤ ∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s := tsum_nonneg (fun s => by positivity)
  unfold annularPowerConstant
  positivity

theorem powerAnnular_finiteCenters_maximum {C η : ℝ} (hC : 0 ≤ C)
    (hBourgain : SmoothCircleBourgainInput C) (hη : 0<η) {M K : ℕ} (hM : 2 ≤ M)
    (Γ : Finset ℚ) (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hcap : ∀ r ∈ Γ,r.den ≤ K)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hc : ∀ r ∈ Γ,‖c r‖ ≤ A*(r.den : ℝ)^(-η))
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (varyingIndexAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (annularPowerConstant C η*A)*‖f‖ := by
  classical
  have hcoef (s : ℕ) (r : ℚ) (hr : r ∈ Γ.filter (fun r => Nat.log2 r.den=s)) :
      ‖c r‖ ≤ A*((2 : ℝ)^s)^(-η) := by
    have hmem := mem_filter.mp hr
    have hb := sourceDyadicRationalCenters_den_bounds
      ((mem_sourceDyadicRationalCenters _ _).mpr ⟨hcan r hmem.1,hmem.2⟩)
    exact (hc r hmem.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hb.1 (neg_nonpos.mpr hη.le)) hA)
  have hex (s : ℕ) := allIndex_annular_truncation_maximum hC hBourgain hM s
    (Γ.filter (fun r => Nat.log2 r.den=s)) (fun r hr => hcan r (mem_filter.mp hr).1)
    (fun r hr => (sourceDyadicRationalCenters_den_bounds ((mem_sourceDyadicRationalCenters _ _).mpr
      ⟨hcan r (mem_filter.mp hr).1,(mem_filter.mp hr).2⟩)).2.le) β hβ0 hβ1 c
    (by positivity : 0 ≤ A*((2 : ℝ)^s)^(-η)) (hcoef s) R hR f
  choose G hG0 hGt hGn using hex
  let S := range (Nat.log2 K+1)
  let g := ∑ s ∈ S,G s
  have heq (j : ℕ) : varyingIndexAnnularBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
      ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c=
      ∑ s ∈ S,weightedAnnularSourceBlock ((Γ.filter (fun r => Nat.log2 r.den=s)).filter
        (fun r => (r.den : ℝ) ≤ R j)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c := by
    unfold varyingIndexAnnularBlock
    rw [rational_dyadic_partition _ K (fun r hr => hcap r (mem_filter.mp hr).1)]
    apply sum_congr rfl
    intro s _
    have hset : (Γ.filter (fun r => (r.den : ℝ) ≤ R j)).filter (fun r => Nat.log2 r.den=s)=
        (Γ.filter (fun r => Nat.log2 r.den=s)).filter (fun r => (r.den : ℝ) ≤ R j) := by
      ext r
      simp only [mem_filter,and_assoc,and_left_comm,and_comm]
    rw [hset]
    apply sum_congr rfl
    intro r hr
    rw [(mem_filter.mp (mem_filter.mp hr).1).2]
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hη
  have hsum := shifted_polynomial_geometric_summable 3 hr0 hr1
  have hK := allIndexAnnularConstant_pos hC
  have hKbound : allIndexAnnularConstant C*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s) ≤
      annularPowerConstant C η := by unfold annularPowerConstant;linarith
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
      _ ≤ ∑ s ∈ S,(allIndexAnnularConstant C*(A*((2 : ℝ)^s)^(-η))*((s : ℝ)+1)^3)*‖f‖ :=
        sum_le_sum (fun s _ => hGn s)
      _ = (allIndexAnnularConstant C*A*‖f‖)*∑ s ∈ S,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s := by
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        rw [dyadic_pow_rpow]
        ring
      _ ≤ (allIndexAnnularConstant C*A*‖f‖)*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s) :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun s _ => by positivity)) (by positivity)
      _ = (allIndexAnnularConstant C*(∑' s : ℕ,((s : ℝ)+1)^3*((2 : ℝ)^(-η))^s))*A*‖f‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKbound hA) (norm_nonneg f)

theorem powerAnnular_countable_maximum {C η : ℝ} (hC : 0 ≤ C)
    (hBourgain : SmoothCircleBourgainInput C) (hη : 0<η) {M : ℕ} (hM : 2 ≤ M)
    (P : ℚ → Prop) [DecidablePred P] (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ r,r ∈ Set.Ico (0 : ℚ) 1 → P r → ‖c r‖ ≤ A*(r.den : ℝ)^(-η))
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (varyingIndexAnnularBlock ((sourceRationalCenters (R j)).filter P)
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (annularPowerConstant C η*A)*‖f‖ := by
  classical
  have hK := annularPowerConstant_pos hC η
  apply finite_family_countable_maximum _ (by positivity)
  intro J
  let K := J.sup (fun j => ⌊R j⌋₊)
  let Γ := (canonicalRationalCenters K).filter P
  have hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 := fun r hr =>
    ((mem_canonicalRationalCenters _ _).mp (mem_filter.mp hr).1).1
  have hcap : ∀ r ∈ Γ,r.den ≤ K := fun r hr =>
    ((mem_canonicalRationalCenters _ _).mp (mem_filter.mp hr).1).2
  obtain ⟨g,hg,ht,hn⟩ := powerAnnular_finiteCenters_maximum hC hBourgain hη hM Γ hcan hcap β hβ0 hβ1 c hA
    (fun r hr => hc r (hcan r hr) (mem_filter.mp hr).2) R hR f
  refine ⟨g,hg,?_,hn⟩
  intro j hj x
  have he : Γ.filter (fun r => (r.den : ℝ) ≤ R j)=(sourceRationalCenters (R j)).filter P := by
    ext r
    simp only [Γ,mem_filter,mem_canonicalRationalCenters,mem_sourceRationalCenters (hR j)]
    constructor
    · rintro ⟨⟨⟨hc,_⟩,hp⟩,hr⟩
      exact ⟨⟨hc,hr⟩,hp⟩
    · rintro ⟨⟨hc,hr⟩,hp⟩
      exact ⟨⟨⟨hc,(Nat.le_floor hr).trans (le_sup (f := fun j => ⌊R j⌋₊) hj)⟩,hp⟩,hr⟩
  rw [←he]
  exact ht j x

end PrimeSquares
