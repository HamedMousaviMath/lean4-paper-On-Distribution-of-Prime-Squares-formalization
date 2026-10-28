import PrimeSquares.RationalFrequencyPeriod

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

/-- Independent rational smooth multifrequency and circle-transference input.
It concerns arbitrary rational centers and the fixed smooth dilation family;
there is no annular kernel, beta, arithmetic coefficient or paper endpoint.
The cited deep rational-frequency theorem and its transference are explicit
hypotheses, not additional Lean axioms or assertions of a proved theorem. -/
def RationalSmoothCircleInput (C : ℝ) : Prop :=
  ∀ Γ : Finset ℚ, (∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1) →
  ∀ P : ℕ, 0<P → (∀ r ∈ Γ,r.den ∣ P) →
  ∀ δ : ℝ, 0<δ → δ≤1 → PeriodicFrequencySeparated Γ δ →
  ∀ (a : ℝ) (ha : 4≤a), 16≤a*δ →
  ∀ J : Finset ℕ, ∀ f : ℓ²(ℤ,ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2,
    (∀ x,0≤g x) ∧
    (∀ j ∈ J,∀ x,‖integerMultiplier (unweightedSmoothCircleFamily Γ a ha j) f x‖≤g x) ∧
    ‖g‖≤C*rationalFrequencyLoss P Γ*‖f‖

theorem rationalSmoothCircle_countable {C : ℝ} (hC : 0≤C) (H : RationalSmoothCircleInput C)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0:ℚ) 1)
    (P : ℕ) (hP : 0<P) (hperiod : ∀ r ∈ Γ,r.den ∣ P)
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (hsep : PeriodicFrequencySeparated Γ δ)
    (a : ℝ) (ha : 4≤a) (hscale : 16≤a*δ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (unweightedSmoothCircleFamily Γ a ha j) f x‖≤g x) ∧
      ‖g‖≤C*rationalFrequencyLoss P Γ*‖f‖ :=
  finite_multiplier_countable_maximum _ (mul_nonneg hC (rationalFrequencyLoss_nonneg hP Γ))
    (H Γ hc P hP hperiod δ hδ hδ1 hsep a ha hscale) f

theorem rational_weightedSource_projection {C : ℝ} (hC : 0≤C) (hB : RationalSmoothCircleInput C)
    {M s : ℕ} (hM : 2≤M) (hs : 2≤s) (Γ : Finset ℚ)
    (P : ℕ) (hP : 0<P) (hperiod : ∀ r ∈ Γ,r.den ∣ P)
    (hc : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hd : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1))
    (hwide : (16 : ℝ)^s≤(M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2≤(M : ℝ)^2)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (hb : ∀ r∈Γ,‖c r‖≤A) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ=>ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (∑ r∈Γ,c r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r) f x‖≤g x) ∧
      ‖g‖≤(C*rationalFrequencyLoss P Γ*A)*‖f‖ := by
  let D : ℝ := (2 : ℝ)^(s+1)
  have hDp : 0<D := by dsimp [D];positivity
  have hD1 : 1≤D := by dsimp [D];exact one_le_pow₀ (by norm_num)
  have hδ : 0<1/D^2 := by positivity
  have hδ1 : 1/D^2≤1 := (div_le_one (by positivity : 0<D^2)).mpr (by nlinarith)
  have hsep : PeriodicFrequencySeparated Γ (1/D^2) := by
    intro r hr t ht hne k
    exact canonical_lift_denominator_bound (hc r hr) (hc t ht) hne (hd r hr) (hd t ht) k
  have hMr : (2 : ℝ)≤M := by exact_mod_cast hM
  have hfour : (4 : ℝ)≤(M : ℝ)^2 := by nlinarith
  have hstart : 16≤(M : ℝ)^2*(1/D^2) := by
    rw [mul_one_div]
    exact (le_div_iff₀ (by positivity : 0<D^2)).mpr hsepScale
  let F := integerMultiplier (weightedSourceCutoff Γ s c) f
  obtain ⟨g,hg,ht,hn⟩ := rationalSmoothCircle_countable hC hB Γ hc P hP hperiod hδ hδ1 hsep
    ((M : ℝ)^2) hfour hstart F
  refine ⟨g,hg,?_,?_⟩
  · intro j x
    have hNj := dyadic_annular_scale_lower hM j
    have hNreal : (2 : ℝ)≤((2 : ℕ)^j*M : ℕ) := by exact_mod_cast hNj
    have ha : 1≤(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by nlinarith
    have heScale : smoothCircleScale ((M : ℝ)^2) j=(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by
      rw [dyadic_square_scale]
      unfold smoothCircleScale
      ring
    have hsc : (16 : ℝ)^s≤(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by
      rw [←heScale]
      exact hwide.trans (smoothCircleScale_ge (sq_nonneg _) j)
    rw [weightedSmoothSource_operator hNj hs Γ hc hd c ha hsc f]
    have he : unweightedSmoothCircleFamily Γ ((M : ℝ)^2) hfour j=
        ∑ r∈Γ,circleSmoothCutoff ((((2 : ℕ)^j*M : ℕ) : ℝ)^2) ha r := by
      unfold unweightedSmoothCircleFamily
      simp only [heScale]
    simpa only [he] using ht j x
  · have hF : ‖F‖≤A*‖f‖ := weightedSourceCutoff_input_norm hs Γ hc hd c hA hb f
    exact hn.trans ((mul_le_mul_of_nonneg_left hF
      (mul_nonneg hC (rationalFrequencyLoss_nonneg hP Γ))).trans_eq (by ring))

theorem rational_largeStart_weightedAnnular_maximum {C : ℝ} (hC : 0 ≤ C)
    (hB : RationalSmoothCircleInput C)
    {M s : ℕ} (hM : 2 ≤ M) (hs : 2 ≤ s) (Γ : Finset ℚ)
    (P : ℕ) (hP : 0<P) (hperiod : ∀ r ∈ Γ,r.den ∣ P)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hwide : (16 : ℝ)^s ≤ (M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2 ≤ (M : ℝ)^2)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier
        (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (A*((1/2)*C*rationalFrequencyLoss P Γ+annularProjectionErrorL2Constant))*‖f‖ := by
  let m := fun j => ∑ r ∈ Γ,c r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := rational_weightedSource_projection hC hB hM hs Γ P hP hperiod hc hd
    hwide hsepScale c hA hb f
  obtain ⟨u,hu,htU,hnU⟩ := scalar_multiplier_majorant m
    (fun j => annularOscillatoryModel ((2 : ℕ)^j*M) (β j) 0)
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (fun j => annularOscillatoryModel_norm_half (dyadic_annular_scale_lower hM j) (hβ1 j) 0)
    f g₀ hg₀ ht₀ hn₀
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := rationalProjectionErrorBlock_maximum hM hs Γ hc hd
    (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j)
    (fun _ => c) hA (fun _ => hb) f
  refine ⟨u+g₁,fun x => add_nonneg (hu x) (hg₁ x),?_,?_⟩
  · intro j x
    rw [weightedAnnularSourceBlock_decomposition,integerMultiplier_add]
    change ‖integerMultiplier (_ • m j) f x+integerMultiplier _ f x‖ ≤ u x+g₁ x
    exact (norm_add_le _ _).trans (add_le_add (htU j x) (ht₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hnU hn₁).trans_eq (by ring))


theorem rational_weightedAnnular_allStartingScales {C : ℝ} (hC : 0 ≤ C)
    (hB : RationalSmoothCircleInput C)
    {M s : ℕ} (hM : 2 ≤ M) (hs : 2 ≤ s) (Γ : Finset ℚ)
    (P : ℕ) (hP : 0<P) (hperiod : ∀ r ∈ Γ,r.den ∣ P)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (A*((3/2 : ℝ)*(2*(s : ℝ)+3)+(1/2)*C*rationalFrequencyLoss P Γ+
        annularProjectionErrorL2Constant))*‖f‖ := by
  let n : ℕ := 2*s+3
  let M' : ℕ := (2 : ℕ)^n*M
  have hM' : 2 ≤ M' := dyadic_annular_scale_lower hM n
  obtain ⟨hw,hscl⟩ := annularLargeStart_budgets hM s
  obtain ⟨u,hu,ht,hn⟩ := rational_largeStart_weightedAnnular_maximum hC hB hM' hs Γ P hP hperiod hc hd hw hscl
    (fun j => β (n+j)) (fun j => hβ0 (n+j)) (fun j => hβ1 (n+j)) c hA hb f
  let T := fun j => integerMultiplier (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c)
  have hT : ∀ j ∈ range n,‖T j‖ ≤ (3/2 : ℝ)*A := by
    intro j _
    exact weightedAnnularSourceBlock_operator_bound (dyadic_annular_scale_lower hM j)
      hs Γ hc hd (hβ1 j) c hA hb
  have htail : ∀ j x,‖T (n+j) f x‖ ≤ u x := by
    intro j x
    dsimp [T]
    simpa only [M',←dyadic_annular_scale_shift] using ht j x
  obtain ⟨g,hg,htg,hng⟩ := initialScale_maximal_completion T n hT f u hu htail hn
  refine ⟨g,hg,htg,?_⟩
  exact hng.trans_eq (by dsimp [n];push_cast;ring)


end PrimeSquares
