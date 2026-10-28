import PrimeSquares.DisjointAEMultiplierAssembly
import PrimeSquares.RationalAnnularTruncationMaximum

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def fixedAnnularMultiplier (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N)
    (s : ℕ) (β : ℝ) (c : ℚ→ℂ) (μ : ℚ→AEBoundedCircleSymbol 1) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  ∑ r ∈ Γ,(integerMultiplier (c r • circleAnnularSource N hN β s r)).comp (aeIntegerMultiplier (μ r))

theorem fixedAnnularMultiplier_disjoint_factor {s : ℕ} (hs : 2≤s)
    (Γ : Finset ℚ) (hc : ∀ r∈Γ,r∈Set.Ico (0:ℚ) 1)
    (hd : ∀ r∈Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (μ : ℚ→AEBoundedCircleSymbol 1)
    (hμ : ∀ r∈Γ,∀ᵐ θ ∂AddCircle.haarAddCircle,circleSourceCutoff s r θ=0 → (μ r).value θ=0) :
    ∃ m : AEBoundedCircleSymbol 1,∀ Δ : Finset ℚ,Δ⊆Γ → ∀ N (hN : 1≤N) β c,
      fixedAnnularMultiplier Δ N hN s β c μ=
        (integerMultiplier (weightedAnnularSourceBlock Δ N hN s β c)).comp (aeIntegerMultiplier m) := by
  classical
  have hP : ∀ r∈Γ,∀ t∈Γ,r≠t → ∀ θ,circleSourceCutoff s r θ=0 ∨ circleSourceCutoff s t θ=0 :=
    fun r hr t ht hrt θ => circleSourceCutoff_disjoint hs (hc r hr) (hc t ht) hrt (hd r hr) (hd t ht) θ
  refine ⟨disjointAEMultiplierSymbol Γ μ (circleSourceCutoff s) hP hμ,?_⟩
  intro Δ hΔ N hN β c
  unfold fixedAnnularMultiplier weightedAnnularSourceBlock
  rw [integerMultiplier_finset_sum,ContinuousLinearMap.finsetSum_comp]
  apply sum_congr rfl
  intro r hr
  apply disjointAEMultiplierSymbol_local_comp Γ μ (circleSourceCutoff s) hP hμ (hΔ hr)
  intro θ hz
  simp only [ContinuousMap.smul_apply,circleAnnularSource_zero_of_cutoff N hN β (by omega) r θ hz,smul_zero]

/-- A finite family argument for the indices where cutoff supports may overlap. -/
theorem fixed_annular_finite_truncation_maximum {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    (s : ℕ) (Γ : Finset ℚ) (hc : ∀ r∈Γ,r∈Set.Ico (0:ℚ) 1)
    (hd : ∀ r∈Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r∈Γ,‖c r‖≤A)
    (μ : ℚ→AEBoundedCircleSymbol 1) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,s≤j → ∀ R,0≤R → ∀ x,‖fixedAnnularMultiplier
        (Γ.filter (fun r => (r.den:ℝ)≤R)) ((2:ℕ)^j) (one_le_pow₀ (by norm_num)) s (β j) c μ f x‖≤g x) ∧
      ‖g‖≤(Γ.card:ℝ)*sourceRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2*‖f‖ := by
  classical
  let K := sourceRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2
  have hk0 := sourceRationalTruncationConstant_pos hC hCb
  have hK : 0≤K := by dsimp [K]; positivity
  have hex (r : ℚ) (hr : r∈Γ) : ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,s≤j → ∀ x,‖integerMultiplier (c r • circleAnnularSource ((2:ℕ)^j)
        (one_le_pow₀ (by norm_num)) (β j) s r) (aeIntegerMultiplier (μ r) f) x‖≤g x) ∧ ‖g‖≤K*‖f‖ := by
    obtain ⟨g,hg,ht,hn⟩ := source_rational_annular_truncation_maximum hC hCb H HB s {r}
      (by simpa only [mem_singleton] using fun t (h:t=r) => h ▸ hc r hr)
      (by simpa only [mem_singleton] using fun t (h:t=r) => h ▸ hd r hr)
      β hβ0 hβ1 c hA (by simpa only [mem_singleton] using fun t (h:t=r) => h ▸ ha r hr)
      (aeIntegerMultiplier (μ r) f)
    refine ⟨g,hg,?_,hn.trans ?_⟩
    · intro j hj x
      have he : ({r}:Finset ℚ).filter (fun t => (t.den:ℝ)≤(r.den:ℝ))={r} := by simp
      have hh := ht j hj (r.den:ℝ) (Nat.cast_nonneg _) x
      simpa only [he,weightedAnnularSourceBlock,sum_singleton] using hh
    · exact mul_le_mul_of_nonneg_left ((aeIntegerMultiplier_norm_le (μ r) f).trans_eq (one_mul _)) hK
  let g : ℚ→lp (fun _ : ℤ => ℝ) 2 := fun r => if hr : r∈Γ then Classical.choose (hex r hr) else 0
  have hg (r : ℚ) (hr : r∈Γ) : (∀ x,0≤g r x) ∧
      (∀ j,s≤j → ∀ x,‖integerMultiplier (c r • circleAnnularSource ((2:ℕ)^j)
        (one_le_pow₀ (by norm_num)) (β j) s r) (aeIntegerMultiplier (μ r) f) x‖≤g r x) ∧ ‖g r‖≤K*‖f‖ := by
    simpa only [g,dite_eq_left hr] using Classical.choose_spec (hex r hr)
  let G : lp (fun _ : ℤ => ℝ) 2 := ∑ r∈Γ,g r
  have hG x : G x=∑ r∈Γ,g r x := by simp only [G,lp.coeFn_sum,Finset.sum_apply]
  refine ⟨G,?_,?_,?_⟩
  · intro x
    rw [hG]
    exact sum_nonneg (fun r hr => (hg r hr).1 x)
  · intro j hj R _ x
    simp only [fixedAnnularMultiplier,_root_.sum_apply,ContinuousLinearMap.comp_apply,lp.coeFn_sum,Finset.sum_apply]
    calc
      _≤∑ r∈Γ.filter (fun r => (r.den:ℝ)≤R),‖integerMultiplier (c r • circleAnnularSource ((2:ℕ)^j)
          (one_le_pow₀ (by norm_num)) (β j) s r) (aeIntegerMultiplier (μ r) f) x‖ := norm_sum_le _ _
      _≤∑ r∈Γ.filter (fun r => (r.den:ℝ)≤R),g r x :=
        sum_le_sum (fun r hr => (hg r (mem_filter.mp hr).1).2.1 j hj x)
      _≤∑ r∈Γ,g r x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun r hr _ => (hg r hr).1 x)
      _=G x := (hG x).symm
  · calc
      ‖G‖≤∑ r∈Γ,‖g r‖ := norm_sum_le _ _
      _≤∑ _r∈Γ,K*‖f‖ := sum_le_sum (fun r hr => (hg r hr).2.2)
      _=_ := by simp only [sum_const,nsmul_eq_mul,K]; ring

noncomputable def fixedRationalTruncationConstant (C Cb : ℝ) : ℝ :=
  25*sourceRationalTruncationConstant C Cb

theorem fixedRationalTruncationConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<fixedRationalTruncationConstant C Cb := by
  unfold fixedRationalTruncationConstant
  exact mul_pos (by norm_num) (sourceRationalTruncationConstant_pos hC hCb)

/-- The full denominator corollary including its fixed measurable multiplier clause. -/
theorem source_fixed_annular_truncation_maximum {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    (s : ℕ) (Γ : Finset ℚ) (hc : ∀ r∈Γ,r∈Set.Ico (0:ℚ) 1)
    (hd : ∀ r∈Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r∈Γ,‖c r‖≤A)
    (μ : ℚ→AEBoundedCircleSymbol 1)
    (hμ : ∀ r∈Γ,∀ᵐ θ ∂AddCircle.haarAddCircle,circleSourceCutoff s r θ=0 → (μ r).value θ=0)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,s≤j → ∀ R,0≤R → ∀ x,‖fixedAnnularMultiplier
        (Γ.filter (fun r => (r.den:ℝ)≤R)) ((2:ℕ)^j) (one_le_pow₀ (by norm_num)) s (β j) c μ f x‖≤g x) ∧
      ‖g‖≤fixedRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2*‖f‖ := by
  classical
  have hk := sourceRationalTruncationConstant_pos hC hCb
  by_cases hs : 2≤s
  · obtain ⟨m,hm⟩ := fixedAnnularMultiplier_disjoint_factor hs Γ hc hd μ hμ
    obtain ⟨g,hg,ht,hn⟩ := source_rational_annular_truncation_maximum hC hCb H HB s Γ hc hd
      β hβ0 hβ1 c hA ha (aeIntegerMultiplier m f)
    refine ⟨g,hg,?_,hn.trans ?_⟩
    · intro j hj R hR x
      rw [hm _ (filter_subset _ _) _ _ _ _,ContinuousLinearMap.comp_apply]
      exact ht j hj R hR x
    · have hh := mul_le_mul_of_nonneg_left ((aeIntegerMultiplier_norm_le m f).trans_eq (one_mul _))
        (show 0≤sourceRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2 by positivity)
      refine hh.trans ?_
      have hp0 : 0≤sourceRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2*‖f‖ := by positivity
      unfold fixedRationalTruncationConstant
      nlinarith only [hp0]
  · have hden : ∀ r∈Γ,r.den≤4 := by
      intro r hr
      have hh : (r.den:ℝ)≤4 := (hd r hr).trans ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : s+1≤2)).trans_eq (by norm_num))
      exact_mod_cast hh
    have hcard : (Γ.card:ℝ)≤25 := by
      have hsub : Γ⊆canonicalRationalCenters 4 := fun r hr => (mem_canonicalRationalCenters _ _).mpr ⟨hc r hr,hden r hr⟩
      have hh := (card_le_card hsub).trans (canonicalRationalCenters_card 4)
      norm_num at hh
      exact_mod_cast hh
    obtain ⟨g,hg,ht,hn⟩ := fixed_annular_finite_truncation_maximum hC hCb H HB s Γ hc hd β hβ0 hβ1 c hA ha μ f
    refine ⟨g,hg,ht,hn.trans ?_⟩
    unfold fixedRationalTruncationConstant
    gcongr

end PrimeSquares
