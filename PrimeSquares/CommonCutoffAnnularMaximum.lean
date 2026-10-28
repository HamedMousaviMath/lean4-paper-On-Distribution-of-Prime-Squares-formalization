import PrimeSquares.CommonCutoffGeometry
import PrimeSquares.AllIndexAnnularTruncationMaximum
import PrimeSquares.IntegerMultiplierComposition

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def weightedWidthAnnularBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (β a : ℝ) (ha : 2≤a) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r∈Γ,c r • circleWidthAnnular N hN β a ha r

theorem common_annular_cross_zero (N : ℕ) (hN : 1≤N) (β : ℝ)
    {a : ℝ} (ha : 4≤a) {s : ℕ} (hs : 2≤s) (hwide : 2*(16 : ℝ)^s≤a)
    {r t : ℚ} (hr : r∈Set.Ico (0 : ℚ) 1) (ht : t∈Set.Ico (0 : ℚ) 1)
    (hne : r≠t) (hrD : (r.den : ℝ)≤(2 : ℝ)^(s+1))
    (htD : (t.den : ℝ)≤(2 : ℝ)^(s+1)) :
    circleAnnularSource N hN β s r*circleSmoothCutoff a (by linarith) t=0 := by
  ext ξ
  rcases circleSourceCutoff_disjoint hs hr ht hne hrD htD ξ with h | h
  · simp only [ContinuousMap.mul_apply,ContinuousMap.zero_apply,
      circleAnnularSource_zero_of_cutoff N hN β (by omega) r ξ h,zero_mul]
  · simp only [ContinuousMap.mul_apply,ContinuousMap.zero_apply,
      circleSmoothCutoff_supported_in_source (by linarith : 1≤a) (by omega) hwide t ξ h,mul_zero]

theorem weightedWidthAnnular_factorization (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (β : ℝ) {a : ℝ} (ha : 4≤a) {s : ℕ} (hs : 2≤s) (hwide : 2*(16 : ℝ)^s≤a)
    (hcan : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hden : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1)) (c : ℚ → ℂ) :
    weightedWidthAnnularBlock Γ N hN β a (by linarith) c=
      weightedAnnularSourceBlock Γ N hN s β c*
        ∑ r∈Γ,circleSmoothCutoff a (by linarith) r := by
  classical
  unfold weightedWidthAnnularBlock weightedAnnularSourceBlock
  rw [sum_mul]
  apply sum_congr rfl
  intro r hr
  rw [mul_sum]
  symm
  calc
    _ = c r • circleAnnularSource N hN β s r*circleSmoothCutoff a (by linarith) r := by
      apply sum_eq_single r
      · intro t ht htr
        rw [smul_mul_assoc,common_annular_cross_zero N hN β ha hs hwide
          (hcan r hr) (hcan t ht) htr.symm (hden r hr) (hden t ht)]
        exact smul_zero (M := ℂ) (A := C(PrimeCircle,ℂ)) (c r)
      · exact fun h => (h hr).elim
    _ = _ := by
      rw [smul_mul_assoc,←circleWidthAnnular_factorization N hN β ha (by omega) hwide r]

theorem common_cutoff_band_maximum {C A a : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) (hA : 0≤A) (ha : 4≤a)
    {M s : ℕ} (hM : 2≤M) (hs : 2≤s) (hwide : 2*(16 : ℝ)^s≤a)
    (Γ : Finset ℚ) (hcan : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hden : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ r∈Γ,‖c r‖≤A) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (weightedWidthAnnularBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a (by linarith) c) f x‖≤g x) ∧
      ‖g‖≤(allIndexAnnularConstant C*A*((s : ℝ)+1)^3)*‖f‖ := by
  classical
  let P := ∑ r∈Γ,circleSmoothCutoff a (by linarith) r
  let v := integerMultiplier P f
  have hv : ‖v‖≤‖f‖ := by
    have hp : ‖integerMultiplier P‖≤1 := common_circle_projection_norm ha hs hwide Γ hcan hden
    exact ((integerMultiplier P).le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _))
  obtain ⟨g,hg,ht,hn⟩ := allIndex_annular_truncation_maximum hC HB hM s Γ hcan hden β hβ0 hβ1
    c hA hc (fun _ => (2 : ℝ)^(s+1)) (fun _ => by positivity) v
  have hΓ : Γ.filter (fun r => (r.den : ℝ)≤(2 : ℝ)^(s+1))=Γ := filter_eq_self.mpr hden
  refine ⟨g,hg,?_,hn.trans ?_⟩
  · intro j x
    have h := ht j x
    rw [hΓ] at h
    rw [weightedWidthAnnular_factorization Γ _ _ _ ha hs hwide hcan hden c,
      ←integerMultiplier_comp_apply]
    exact h
  · exact mul_le_mul_of_nonneg_left hv (by
      have h := allIndexAnnularConstant_pos hC
      positivity)

end PrimeSquares
