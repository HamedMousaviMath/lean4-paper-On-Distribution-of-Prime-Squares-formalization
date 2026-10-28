import PrimeSquares.RationalAnnularSourceMaximum
import PrimeSquares.WeightedAnnularTruncationMaximum

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def rationalAnnularTruncationConstant (C Cb : ℝ) : ℝ :=
  3*rationalAnnularConstant C Cb

theorem rationalAnnularTruncationConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<rationalAnnularTruncationConstant C Cb := by
  unfold rationalAnnularTruncationConstant
  exact mul_pos (by norm_num) (rationalAnnularConstant_pos hC hCb)

theorem rational_weightedAnnular_truncation_maximum {C Cb : ℝ} (hC : 0 ≤ C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb) {M s : ℕ} (hM : 2 ≤ M) (hs : 4 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j R,0 ≤ R → ∀ x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R)) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (rationalAnnularTruncationConstant C Cb*A*((s : ℝ)+1)^2)*‖f‖ := by
  obtain ⟨ht,hst,hw⟩ := predecessorSourceCutoff_geometry hs
  let F := fun j r => c r • circleAnnularSource ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r
  let P := circleSourceCutoff (s-1)
  let B := rationalAnnularConstant C Cb*A*((s:ℝ)+1)
  have hlocal : ∀ j,∀ r ∈ Γ,F j r=F j r*P r := by
    intro j r _
    dsimp [F,P]
    calc
      _=c r • (circleAnnularSource ((2 : ℕ)^j*M) _ (β j) s r*circleSourceCutoff (s-1) r) :=
        congrArg (fun z => c r • z) (circleAnnularSource_localized _ (by omega) ht hst (β j) r)
      _=_ := (smul_mul_assoc _ _ _).symm
  have hP : ∀ r ∈ Γ,∀ u ∈ Γ,r ≠ u → ∀ θ,P r θ=0 ∨ P u θ=0 := by
    intro r hr u hu hne θ
    exact circleSourceCutoff_general_disjoint (hc r hr) (hc u hu) hne (hd r hr) (hd u hu) hw θ
  have hMax : ∀ Δ : Finset ℚ,Δ ⊆ Γ → ∀ v : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
        (∀ j x,‖integerMultiplier (∑ r ∈ Δ,F j r) v x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖v‖ := by
    intro Δ hΔ v
    exact rational_annular_allStarting hC hCb H HB hM s Δ
      (fun r hr => hc r (hΔ hr)) (fun r hr => hd r (hΔ hr)) β hβ0 hβ1 c hA
      (fun r hr => hb r (hΔ hr)) v
  have hh : (2 : ℕ)^(s+1)+1 ≤ (2 : ℕ)^(s+2) := by
    have hp : (1 : ℕ) ≤ (2 : ℕ)^(s+1) := Nat.one_le_pow _ _ (by norm_num)
    rw [show s+2=(s+1)+1 by omega,pow_succ]
    omega
  obtain ⟨g,hg,htg,hng⟩ := finiteFrequency_denominator_maximum Γ ((2 : ℕ)^(s+1)) (s+2)
    (fun r hr => by exact_mod_cast hd r hr) hh F P hlocal hP
    (fun r _ θ => circleSourceCutoff_pointwise_norm ht r θ)
    (show 0 ≤ B from mul_nonneg (mul_nonneg (rationalAnnularConstant_pos hC hCb).le hA) (by positivity)) hMax f
  refine ⟨g,hg,htg,hng.trans ?_⟩
  have hk := (rationalAnnularConstant_pos hC hCb).le
  have hs0 : (0:ℝ)≤s := Nat.cast_nonneg s
  have hdepth : ((s+2+1:ℕ):ℝ)≤3*((s:ℝ)+1) := by push_cast; linarith
  have hh := mul_le_mul_of_nonneg_right hdepth (show 0≤B from
    mul_nonneg (mul_nonneg hk hA) (by positivity))
  have hh' := mul_le_mul_of_nonneg_right hh (norm_nonneg f)
  dsimp [B] at hh' ⊢
  unfold rationalAnnularTruncationConstant
  push_cast at hh' ⊢
  nlinarith only [hh']

noncomputable def rationalAllTruncationConstant (C Cb : ℝ) : ℝ :=
  1+rationalAnnularTruncationConstant C Cb+33*allIndexAnnularConstant Cb

theorem rationalAllTruncationConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<rationalAllTruncationConstant C Cb := by
  have h1 := rationalAnnularTruncationConstant_pos hC hCb
  have h2 := allIndexAnnularConstant_pos hCb
  unfold rationalAllTruncationConstant
  positivity

theorem rational_smallIndex_all_thresholds {Cb : ℝ} (hCb : 0≤Cb) (HB : SmoothCircleBourgainInput Cb)
    {M s : ℕ} (hM : 2≤M) (hs : s≤4) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1) (hd : ∀ r ∈ Γ,(r.den:ℝ)≤32)
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j R,0≤R → ∀ x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den:ℝ)≤R)) ((2:ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j; omega) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤(33*allIndexAnnularConstant Cb*A)*‖f‖ := by
  classical
  have hex (k : Fin 33) : ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den:ℝ)≤(k.val:ℝ))) ((2:ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j; omega) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤allIndexAnnularConstant Cb*A*‖f‖ :=
    smallIndex_annular_truncation_maximum hCb HB hM hs Γ hc hd β hβ0 hβ1 c hA ha
      (fun _ => (k.val:ℝ)) (fun _ => Nat.cast_nonneg _) f
  choose g hg0 hgt hgn using hex
  let G : lp (fun _ : ℤ => ℝ) 2 := ∑ k : Fin 33,g k
  have hG (x : ℤ) : G x=∑ k : Fin 33,g k x := by simp only [G,lp.coeFn_sum,Finset.sum_apply]
  refine ⟨G,?_,?_,?_⟩
  · intro x
    rw [hG]
    exact sum_nonneg (fun k _ => hg0 k x)
  · intro j R hR x
    let k : Fin 33 := ⟨min 32 ⌊R⌋₊,by omega⟩
    have hf : Γ.filter (fun r => (r.den:ℝ)≤R)=Γ.filter (fun r => (r.den:ℝ)≤(k.val:ℝ)) := by
      ext r
      simp only [mem_filter]
      constructor
      · rintro ⟨hr,hden⟩
        refine ⟨hr,?_⟩
        have hh : r.den≤min 32 ⌊R⌋₊ := le_min (by exact_mod_cast hd r hr) (Nat.le_floor hden)
        exact_mod_cast hh
      · rintro ⟨hr,hden⟩
        refine ⟨hr,hden.trans ?_⟩
        exact (show (k.val:ℝ)≤(⌊R⌋₊:ℝ) by exact_mod_cast min_le_right 32 ⌊R⌋₊).trans (Nat.floor_le hR)
    rw [hf]
    exact (hgt k j x).trans (by rw [hG]; exact single_le_sum (fun i _ => hg0 i x) (mem_univ k))
  · calc
      _ ≤ ∑ k : Fin 33,‖g k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin 33,allIndexAnnularConstant Cb*A*‖f‖ := sum_le_sum (fun k _ => hgn k)
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem rational_annular_all_thresholds {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    {M : ℕ} (hM : 2≤M) (s : ℕ) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1) (hd : ∀ r ∈ Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j R,0≤R → ∀ x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den:ℝ)≤R)) ((2:ℕ)^j*M)
          (by have hh := dyadic_annular_scale_lower hM j; omega) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤rationalAllTruncationConstant C Cb*A*((s:ℝ)+1)^2*‖f‖ := by
  have hk := rationalAnnularTruncationConstant_pos hC hCb
  have hb := allIndexAnnularConstant_pos hCb
  have hs0 : (0:ℝ)≤s := Nat.cast_nonneg s
  by_cases hs : 4≤s
  · obtain ⟨g,hg,ht,hn⟩ := rational_weightedAnnular_truncation_maximum hC hCb H HB hM hs Γ hc hd
      β hβ0 hβ1 c hA ha f
    have hconst : rationalAnnularTruncationConstant C Cb≤rationalAllTruncationConstant C Cb := by
      unfold rationalAllTruncationConstant
      linarith
    refine ⟨g,hg,ht,hn.trans ?_⟩
    gcongr
  · have hden32 : ∀ r ∈ Γ,(r.den:ℝ)≤32 := by
      intro r hr
      exact (hd r hr).trans ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
        (by omega : s+1≤5)).trans_eq (by norm_num))
    obtain ⟨g,hg,ht,hn⟩ := rational_smallIndex_all_thresholds hCb HB hM (by omega : s≤4) Γ hc hden32
      β hβ0 hβ1 c hA ha f
    have hconst : 33*allIndexAnnularConstant Cb≤rationalAllTruncationConstant C Cb := by
      unfold rationalAllTruncationConstant
      linarith
    have hp : (1:ℝ)≤((s:ℝ)+1)^2 := by nlinarith
    refine ⟨g,hg,ht,hn.trans ?_⟩
    have hh := mul_le_mul_of_nonneg_right hconst hA
    have hh' := le_mul_of_one_le_right
      (mul_nonneg (rationalAllTruncationConstant_pos hC hCb).le hA) hp
    exact mul_le_mul_of_nonneg_right (hh.trans hh') (norm_nonneg f)

noncomputable def sourceRationalTruncationConstant (C Cb : ℝ) : ℝ :=
  81+rationalAllTruncationConstant C Cb

theorem sourceRationalTruncationConstant_pos {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb) :
    0<sourceRationalTruncationConstant C Cb := by
  have hk := rationalAllTruncationConstant_pos hC hCb
  unfold sourceRationalTruncationConstant
  positivity

/-- One majorant for the simultaneous time and real denominator suprema. -/
theorem source_rational_annular_truncation_maximum {C Cb : ℝ} (hC : 0≤C) (hCb : 0≤Cb)
    (H : RationalSmoothCircleInput C) (HB : SmoothCircleBourgainInput Cb)
    (s : ℕ) (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den:ℝ)≤(2:ℝ)^(s+1))
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (ha : ∀ r ∈ Γ,‖c r‖≤A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j,s≤j → ∀ R,0≤R → ∀ x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den:ℝ)≤R)) ((2:ℕ)^j)
          (one_le_pow₀ (by norm_num)) s (β j) c) f x‖≤g x) ∧
      ‖g‖≤sourceRationalTruncationConstant C Cb*A*((s:ℝ)+1)^2*‖f‖ := by
  classical
  have hk := rationalAllTruncationConstant_pos hC hCb
  cases s with
  | zero =>
    have hcard : (Γ.card:ℝ)≤9 := by
      have hsub : Γ⊆canonicalRationalCenters 2 := by
        intro r hr
        exact (mem_canonicalRationalCenters _ _).mpr ⟨hc r hr,by exact_mod_cast hd r hr⟩
      have hh := (card_le_card hsub).trans (canonicalRationalCenters_card 2)
      norm_num at hh
      exact_mod_cast hh
    let T := fun k : ℕ => integerMultiplier
      (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den:ℝ)≤(k:ℝ))) 1 (by norm_num) 0 (β 0) c)
    let v := finiteOperatorEnvelope (range 3) T f
    have hv0 := finiteOperatorEnvelope_nonneg (range 3) T f
    have hT : ∀ k ∈ range 3,‖T k‖≤27*A := by
      intro k _
      have hh := weightedAnnularSource_initial_operator_norm (hβ0 0) (hβ1 0) 0
        (Γ.filter (fun r => (r.den:ℝ)≤(k:ℝ))) c hA (fun r hr => ha r (mem_filter.mp hr).1)
      have hcf : ((Γ.filter (fun r => (r.den:ℝ)≤(k:ℝ))).card:ℝ)≤Γ.card := by exact_mod_cast card_filter_le Γ _
      exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right (hcf.trans hcard) hA])
    have hvn : ‖v‖≤81*A*‖f‖ := by
      have hh := finiteOperatorEnvelope_norm (range 3) T (fun _ => 27*A) hT f
      calc
        ‖v‖ ≤ (3:ℝ)*(27*A)*‖f‖ := by simpa only [v,sum_const,card_range,nsmul_eq_mul,Nat.cast_ofNat] using hh
        _ = _ := by ring
    obtain ⟨u,hu,htu,hnu⟩ := rational_annular_all_thresholds hC hCb H HB (by norm_num : 2≤(2:ℕ)) 0 Γ hc hd
      (fun j => β (1+j)) (fun j => hβ0 (1+j)) (fun j => hβ1 (1+j)) c hA ha f
    refine ⟨v+u,fun x => add_nonneg (hv0 x) (hu x),?_,?_⟩
    · intro j _ R hR x
      change _≤v x+u x
      cases j with
      | zero =>
        let k := min 2 ⌊R⌋₊
        have hf : Γ.filter (fun r => (r.den:ℝ)≤R)=Γ.filter (fun r => (r.den:ℝ)≤(k:ℝ)) := by
          ext r
          simp only [mem_filter]
          constructor
          · rintro ⟨hr,hrR⟩
            exact ⟨hr,by exact_mod_cast le_min (by exact_mod_cast hd r hr) (Nat.le_floor hrR)⟩
          · rintro ⟨hr,hrK⟩
            exact ⟨hr,hrK.trans ((show (k:ℝ)≤(⌊R⌋₊:ℝ) by exact_mod_cast min_le_right 2 ⌊R⌋₊).trans (Nat.floor_le hR))⟩
        rw [hf]
        exact (finiteOperatorEnvelope_dominates (range 3) T f (show k∈range 3 by simp only [mem_range]; dsimp [k]; omega) x).trans
          (le_add_of_nonneg_right (hu x))
      | succ j =>
        have he : (2:ℕ)^(1+j)=(2:ℕ)^j*2 := by rw [Nat.add_comm 1 j,pow_succ]
        have hh := htu j R hR x
        apply le_trans ?_ (le_add_of_nonneg_left (hv0 x))
        simpa only [Nat.add_comm j 1,he] using hh
    · have hn := (norm_add_le v u).trans (add_le_add hvn hnu)
      exact hn.trans_eq (by unfold sourceRationalTruncationConstant; norm_num only [Nat.cast_zero,zero_add,one_pow,mul_one]; ring)
  | succ s =>
    have hM : 2≤(2:ℕ)^(s+1) := by
      calc
        2 = (2:ℕ)^1 := by norm_num
        _ ≤ (2:ℕ)^(s+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g,hg,ht,hn⟩ := rational_annular_all_thresholds hC hCb H HB hM (s+1) Γ hc hd
      (fun j => β (j+(s+1))) (fun j => hβ0 (j+(s+1))) (fun j => hβ1 (j+(s+1))) c hA ha f
    refine ⟨g,hg,?_,hn.trans ?_⟩
    · intro j hj R hR x
      have he : (2:ℕ)^(j-(s+1))*(2:ℕ)^(s+1)=(2:ℕ)^j := by rw [←pow_add,Nat.sub_add_cancel hj]
      simpa only [he,Nat.sub_add_cancel hj] using ht (j-(s+1)) R hR x
    · have hh : rationalAllTruncationConstant C Cb≤sourceRationalTruncationConstant C Cb := by
        unfold sourceRationalTruncationConstant
        linarith
      gcongr

end PrimeSquares
