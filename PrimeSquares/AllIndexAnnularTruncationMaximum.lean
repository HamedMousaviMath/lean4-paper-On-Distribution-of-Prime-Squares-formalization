import PrimeSquares.SmallSourceCutoffDifference
import PrimeSquares.WeightedAnnularTruncationMaximum
import PrimeSquares.CircleEnergyMaximalWitness

open Finset
open scoped lp
namespace PrimeSquares

theorem dyadic_inverse_square_bound {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    (1 : ℝ)/(((2 : ℕ)^j*M : ℕ) : ℝ)^2 ≤ (1/4 : ℝ)^j := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have he : ((((2 : ℕ)^j*M : ℕ) : ℝ)^2)=(4 : ℝ)^j*(M : ℝ)^2 := by
    push_cast
    rw [mul_pow,←pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  rw [he]
  calc
    _ ≤ 1/(4 : ℝ)^j := one_div_le_one_div_of_le (by positivity)
      (le_mul_of_one_le_right (by positivity) (by nlinarith : (1 : ℝ) ≤ (M : ℝ)^2))
    _ = _ := by rw [one_div_pow]

theorem geometric_symbol_maximum (m : ℕ → C(PrimeCircle,ℂ)) {b : ℝ} (hb : 0 ≤ b)
    (hm : ∀ j θ,‖m j θ‖ ≤ b*(1/4 : ℝ)^j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (m j) f x‖ ≤ g x) ∧ ‖g‖ ≤ (2*b)*‖f‖ := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1/16 : ℝ)) (by norm_num)
  have he (J : Finset ℕ) (θ : PrimeCircle) : (∑ j ∈ J,‖m j θ‖^2) ≤ (2*b)^2 := by
    have hsum : (∑ j ∈ J,(1/16 : ℝ)^j) ≤ 16/15 := by
      have h := hg.summable.sum_le_tsum J (fun j _ => by positivity)
      norm_num [hg.tsum_eq] at h ⊢
      exact h
    calc
      _ ≤ ∑ j ∈ J,(b*(1/4 : ℝ)^j)^2 := sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hm j θ) 2)
      _ = b^2*∑ j ∈ J,(1/16 : ℝ)^j := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        rw [mul_pow,←pow_mul,Nat.mul_comm j 2,pow_mul]
        norm_num
      _ ≤ b^2*(16/15) := mul_le_mul_of_nonneg_left hsum (sq_nonneg b)
      _ ≤ _ := by nlinarith [sq_nonneg b]
  obtain ⟨g,_,h0,ht,hn⟩ := circle_energy_maximal_witness m (by positivity : 0 ≤ 2*b) he f
  exact ⟨g,h0,ht,hn⟩

theorem weightedSmallSource_difference_bound {N s : ℕ} (hN : 2 ≤ N) (hs : s ≤ 4)
    (Γ : Finset ℚ) {β A : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (c : ℚ → ℂ) (hc : ∀ r ∈ Γ,‖c r‖ ≤ A) :
    ‖weightedAnnularSourceBlock Γ N (by omega) s β c-weightedAnnularSourceBlock Γ N (by omega) 4 β c‖ ≤
      (Γ.card : ℝ)*A*smallSourceDifferenceConstant/(N : ℝ)^2 := by
  unfold weightedAnnularSourceBlock
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ Γ,‖c r • circleAnnularSource N (by omega) β s r-c r • circleAnnularSource N (by omega) β 4 r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Γ,A*(smallSourceDifferenceConstant/(N : ℝ)^2) := by
      apply sum_le_sum
      intro r hr
      have he : c r • circleAnnularSource N (by omega) β s r-c r • circleAnnularSource N (by omega) β 4 r=
          c r • (circleAnnularSource N (by omega) β s r-circleAnnularSource N (by omega) β 4 r) := by
        ext θ
        simp only [ContinuousMap.smul_apply,ContinuousMap.sub_apply,smul_eq_mul]
        ring
      rw [he,norm_smul]
      exact mul_le_mul (hc r hr) (circleAnnularSource_small_difference hN hs hβ0 hβ1 r)
        (norm_nonneg _) hA
    _ = _ := by rw [sum_const,nsmul_eq_mul];ring

noncomputable def allIndexAnnularConstant (C : ℝ) : ℝ :=
  1+125*annularTruncationConstant C+2178*smallSourceDifferenceConstant

theorem allIndexAnnularConstant_pos {C : ℝ} (hC : 0 ≤ C) : 0<allIndexAnnularConstant C := by
  have h := annularTruncationConstant_nonneg hC
  have hs := smallSourceDifferenceConstant_pos
  unfold allIndexAnnularConstant
  positivity

theorem smallIndex_annular_truncation_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2 ≤ M) (hs : s ≤ 4) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ 32)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hc : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (allIndexAnnularConstant C*A)*‖f‖ := by
  classical
  have hK := annularTruncationConstant_nonneg hC
  have hsC := smallSourceDifferenceConstant_pos
  have hcard : (Γ.card : ℝ) ≤ 1089 := by
    have hsub : Γ ⊆ canonicalRationalCenters 32 := by
      intro r hr
      exact (mem_canonicalRationalCenters _ _).mpr ⟨hcan r hr,by exact_mod_cast hden r hr⟩
    have h := (card_le_card hsub).trans (canonicalRationalCenters_card 32)
    norm_num at h
    exact_mod_cast h
  obtain ⟨g4,hg4,ht4,hn4⟩ := weightedAnnular_truncation_maximum hC hBourgain hM (by norm_num : 4 ≤ (4 : ℕ))
    Γ hcan (by simpa only [show (2 : ℝ)^(4+1)=32 by norm_num] using hden) β hβ0 hβ1 c hA hc f
  let m := fun j => weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
    ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c-
      weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) 4 (β j) c
  have hb : 0 ≤ (Γ.card : ℝ)*A*smallSourceDifferenceConstant := by positivity
  have hm (j : ℕ) (θ : PrimeCircle) : ‖m j θ‖ ≤ ((Γ.card : ℝ)*A*smallSourceDifferenceConstant)*(1/4 : ℝ)^j := by
    have h := weightedSmallSource_difference_bound (dyadic_annular_scale_lower hM j) hs
      (Γ.filter (fun r => (r.den : ℝ) ≤ R j)) (hβ0 j) (hβ1 j) hA c (fun r hr => hc r (mem_filter.mp hr).1)
    have hcount : ((Γ.filter (fun r => (r.den : ℝ) ≤ R j)).card : ℝ) ≤ Γ.card := by exact_mod_cast card_filter_le Γ _
    have hn := (ContinuousMap.norm_coe_le_norm (m j) θ).trans h
    calc
      _ ≤ ((Γ.card : ℝ)*A*smallSourceDifferenceConstant)/((((2 : ℕ)^j*M : ℕ) : ℝ)^2) :=
        hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount hA) hsC.le) (sq_nonneg _))
      _ ≤ _ := by
        rw [div_eq_mul_inv,←one_div]
        exact mul_le_mul_of_nonneg_left (dyadic_inverse_square_bound (by omega : 1 ≤ M) j) hb
  obtain ⟨ge,hge,hte,hne⟩ := geometric_symbol_maximum m hb hm f
  refine ⟨g4+ge,fun x => add_nonneg (hg4 x) (hge x),?_,?_⟩
  · intro j x
    have he : weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c=
      weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) 4 (β j) c+m j := by dsimp [m];abel
    rw [he,integerMultiplier_add,_root_.add_apply,lp.coeFn_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (ht4 j (R j) (hR j) x) (hte j x))
  · have hcount := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 2*A*smallSourceDifferenceConstant by positivity)
    have hn := (norm_add_le _ _).trans (add_le_add hn4 hne)
    norm_num only [Nat.cast_ofNat] at hn
    have hh : annularTruncationConstant C*A*((4 : ℝ)+1)^3+2*((Γ.card : ℝ)*A*smallSourceDifferenceConstant) ≤
        allIndexAnnularConstant C*A := by unfold allIndexAnnularConstant;nlinarith
    exact hn.trans (by nlinarith only [mul_le_mul_of_nonneg_right hh (norm_nonneg f)])

theorem allIndex_annular_truncation_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M : ℕ} (hM : 2 ≤ M) (s : ℕ) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hc : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (allIndexAnnularConstant C*A*((s : ℝ)+1)^3)*‖f‖ := by
  by_cases hs : 4 ≤ s
  · obtain ⟨g,hg,ht,hn⟩ := weightedAnnular_truncation_maximum hC hBourgain hM hs Γ hcan hden β hβ0 hβ1 c hA hc f
    have hK := annularTruncationConstant_nonneg hC
    have hS := smallSourceDifferenceConstant_pos
    have hconst : annularTruncationConstant C ≤ allIndexAnnularConstant C := by unfold allIndexAnnularConstant;nlinarith
    exact ⟨g,hg,fun j x => ht j (R j) (hR j) x,hn.trans (by gcongr)⟩
  · have hs4 : s ≤ 4 := by omega
    have hden32 : ∀ r ∈ Γ,(r.den : ℝ) ≤ 32 := by
      intro r hr
      exact (hden r hr).trans ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : s+1 ≤ 5)).trans_eq (by norm_num))
    obtain ⟨g,hg,ht,hn⟩ := smallIndex_annular_truncation_maximum hC hBourgain hM hs4 Γ hcan hden32 β hβ0 hβ1 c hA hc R hR f
    have hconst := allIndexAnnularConstant_pos hC
    have hp : (1 : ℝ) ≤ ((s : ℝ)+1)^3 := one_le_pow₀ (by have h := Nat.cast_nonneg (α := ℝ) s;linarith)
    refine ⟨g,hg,ht,hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hp) (norm_nonneg f)

end PrimeSquares
