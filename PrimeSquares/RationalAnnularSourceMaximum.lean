import PrimeSquares.RationalSmoothWeighted
import PrimeSquares.AllIndexAnnularTruncationMaximum
import PrimeSquares.ContinuousAnnularInitialIncrement

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def rationalAnnularConstant (C Cb : ℝ) : ℝ :=
  5+6*C+annularProjectionErrorL2Constant+allIndexAnnularConstant Cb

theorem rationalAnnularConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<rationalAnnularConstant C Cb := by
  have he := annularProjectionErrorL2Constant_pos
  have hb := allIndexAnnularConstant_pos hCb
  unfold rationalAnnularConstant
  positivity

theorem rational_annular_allStarting {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    {M : ℕ} (hM : 2≤M) (s : ℕ) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock Γ ((2:ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j; omega) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤rationalAnnularConstant C Cb*A*((s:ℝ)+1)*‖f‖ := by
  classical
  have he := annularProjectionErrorL2Constant_pos
  have hb := allIndexAnnularConstant_pos hCb
  have hs0 : (0:ℝ)≤s := Nat.cast_nonneg s
  by_cases hs : 2≤s
  · obtain ⟨hP,hper⟩ := rationalBand_common_period s Γ hd
    obtain ⟨g,hg,ht,hn⟩ := rational_weightedAnnular_allStartingScales hC H hM hs Γ
      ((2:ℕ)^(s+1)).factorial hP hper hc hd β hβ0 hβ1 c hA ha f
    have hl := rationalBand_loss_linear s Γ hc hd
    have hl' := mul_le_mul_of_nonneg_left hl (show 0≤(1/2:ℝ)*C by positivity)
    have hlin : (3/2:ℝ)*(2*(s:ℝ)+3)≤5*((s:ℝ)+1) := by linarith
    have hE : annularProjectionErrorL2Constant≤annularProjectionErrorL2Constant*((s:ℝ)+1) :=
      le_mul_of_one_le_right he.le (by linarith)
    have hcost : (3/2:ℝ)*(2*(s:ℝ)+3)+(1/2)*C*rationalFrequencyLoss ((2:ℕ)^(s+1)).factorial Γ+
        annularProjectionErrorL2Constant≤rationalAnnularConstant C Cb*((s:ℝ)+1) := by
      unfold rationalAnnularConstant
      have hb' := mul_nonneg hb.le (show 0≤(s:ℝ)+1 by positivity)
      have hC' := mul_nonneg hC (show 0≤(s:ℝ)+1 by positivity)
      nlinarith
    refine ⟨g,hg,ht,hn.trans ?_⟩
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA) (norm_nonneg f)
    nlinarith only [hh]
  · have hs4 : s≤4 := by omega
    have hden32 : ∀ r ∈ Γ,(r.den:ℝ)≤32 := by
      intro r hr
      exact (hd r hr).trans ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
        (by omega : s+1≤5)).trans_eq (by norm_num))
    have hf : Γ.filter (fun r => (r.den:ℝ)≤32)=Γ := filter_eq_self.mpr hden32
    obtain ⟨g,hg,ht,hn⟩ := smallIndex_annular_truncation_maximum hCb HB hM hs4 Γ hc hden32
      β hβ0 hβ1 c hA ha (fun _ => 32) (fun _ => by norm_num) f
    refine ⟨g,hg,?_,hn.trans ?_⟩
    · intro j x
      simpa only [hf] using ht j x
    · have hk : allIndexAnnularConstant Cb≤rationalAnnularConstant C Cb := by
        unfold rationalAnnularConstant
        linarith
      have hh := mul_le_mul_of_nonneg_right hk hA
      have hh' := le_mul_of_one_le_right
        (show 0≤rationalAnnularConstant C Cb*A from mul_nonneg (rationalAnnularConstant_pos hC hCb).le hA) (show 1≤(s:ℝ)+1 by linarith)
      exact mul_le_mul_of_nonneg_right (hh.trans hh') (norm_nonneg f)

theorem circleAnnularSource_initial_norm {β : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1)
    (s : ℕ) (r : ℚ) : ‖circleAnnularSource 1 (by norm_num) β s r‖≤3 := by
  have hreal (x : ℝ) : ‖localizedAnnularSource 1 (by norm_num) β s x‖≤1 := by
    change ‖annularOscillatoryModel 1 β x*Complex.ofReal (sourceArcCutoffScale s x)‖≤1
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,
      abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans
      (by simpa only [mul_one] using annularOscillatoryModel_norm_one (by norm_num) hβ0 hβ1 x)
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ)≤3)).mpr
  intro θ
  have hh := compactCircleLift_norm_bound (localizedAnnularSource 1 (by norm_num) β s)
    (localizedAnnularSource_support 1 (by norm_num) β s) hreal (θ-((r:ℝ):PrimeCircle))
  simpa only [circleAnnularSource,ContinuousMap.comp_apply,ContinuousMap.coe_mk,mul_one] using hh

theorem weightedAnnularSource_initial_operator_norm {β A : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1)
    (s : ℕ) (Γ : Finset ℚ) (c : ℚ→ℂ) (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A) :
    ‖integerMultiplier (weightedAnnularSourceBlock Γ 1 (by norm_num) s β c)‖≤3*(Γ.card:ℝ)*A := by
  apply (integerMultiplier_opNorm_le _).trans
  unfold weightedAnnularSourceBlock
  calc
    _ ≤ ∑ r ∈ Γ,‖c r • circleAnnularSource 1 (by norm_num) β s r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Γ,A*3 := by
      apply sum_le_sum
      intro r hr
      rw [norm_smul]
      exact mul_le_mul (ha r hr) (circleAnnularSource_initial_norm hβ0 hβ1 s r) (norm_nonneg _) hA
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

noncomputable def sourceRationalAnnularConstant (C Cb : ℝ) : ℝ :=
  27+rationalAnnularConstant C Cb

theorem sourceRationalAnnularConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<sourceRationalAnnularConstant C Cb := by
  have hh := rationalAnnularConstant_pos hC hCb
  unfold sourceRationalAnnularConstant
  positivity

/-- Full source starting range, small denominator indices and scale1 included. -/
theorem source_rational_annular_maximum {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    (s : ℕ) (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,s≤j → ∀ x,‖integerMultiplier (weightedAnnularSourceBlock Γ ((2:ℕ)^j)
        (one_le_pow₀ (by norm_num)) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤sourceRationalAnnularConstant C Cb*A*((s:ℝ)+1)*‖f‖ := by
  have hK := rationalAnnularConstant_pos hC hCb
  cases s with
  | zero =>
    have hcard : (Γ.card:ℝ)≤9 := by
      have hsub : Γ⊆canonicalRationalCenters 2 := by
        intro r hr
        exact (mem_canonicalRationalCenters _ _).mpr ⟨hc r hr,by exact_mod_cast hd r hr⟩
      have hh := (card_le_card hsub).trans (canonicalRationalCenters_card 2)
      norm_num at hh
      exact_mod_cast hh
    obtain ⟨u,hu,htu,hnu⟩ := rational_annular_allStarting hC hCb H HB (by norm_num : 2≤(2:ℕ)) 0 Γ hc hd
      (fun j => β (1+j)) (fun j => hβ0 (1+j)) (fun j => hβ1 (1+j)) c hA ha f
    let T := fun j => integerMultiplier (weightedAnnularSourceBlock Γ ((2:ℕ)^j)
      (one_le_pow₀ (by norm_num)) 0 (β j) c)
    have hT : ∀ j ∈ range 1,‖T j‖≤27*A := by
      intro j hj
      have hj0 : j=0 := by have hj1 := mem_range.mp hj; omega
      subst j
      have hh := weightedAnnularSource_initial_operator_norm (hβ0 0) (hβ1 0) 0 Γ c hA ha
      exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcard hA])
    have htail : ∀ j x,‖T (1+j) f x‖≤u x := by
      intro j x
      have he : (2:ℕ)^(1+j)=(2:ℕ)^j*2 := by rw [Nat.add_comm,pow_add]; norm_num
      simpa only [T,he] using htu j x
    obtain ⟨g,hg,ht,hn⟩ := initialScale_maximal_completion T 1 hT f u hu htail hnu
    refine ⟨g,hg,fun j _ x => ht j x,?_⟩
    exact hn.trans_eq (by unfold sourceRationalAnnularConstant; norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,mul_one,one_mul]; ring)
  | succ s =>
    have hM : 2≤(2:ℕ)^(s+1) := by
      calc
        2 = (2:ℕ)^1 := by norm_num
        _ ≤ (2:ℕ)^(s+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g,hg,ht,hn⟩ := rational_annular_allStarting hC hCb H HB hM (s+1) Γ hc hd
      (fun j => β (j+(s+1))) (fun j => hβ0 (j+(s+1))) (fun j => hβ1 (j+(s+1))) c hA ha f
    refine ⟨g,hg,?_,hn.trans ?_⟩
    · intro j hj x
      have he : (2:ℕ)^(j-(s+1))*(2:ℕ)^(s+1)=(2:ℕ)^j := by rw [←pow_add,Nat.sub_add_cancel hj]
      simpa only [he,Nat.sub_add_cancel hj] using ht (j-(s+1)) x
    · have hh : rationalAnnularConstant C Cb≤sourceRationalAnnularConstant C Cb := by
        unfold sourceRationalAnnularConstant
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh hA) (by positivity)) (norm_nonneg f)

end PrimeSquares
