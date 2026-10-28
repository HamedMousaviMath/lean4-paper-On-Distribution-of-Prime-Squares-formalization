import PrimeSquares.IWCommonCutoffTails
import PrimeSquares.SmallSourceCutoffDifference

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem annular_common_source_difference {N s : ℕ} (hN : 2≤N)
    {β a : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (ha : 2≤a) (hscale : (16 : ℝ)^s≤a) (x : ℝ) :
    ‖(localizedAnnularSource N (by omega) β s-annularCutoffSymbol N (by omega) β a) x‖≤
      4*a/(Real.pi*(N : ℝ)^2) := by
  have hap : 0<a := by linarith
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  by_cases hx : |x|≤1/(2*a)
  · have hc : sourceArcCutoff (a*x)=1 := by
      apply sourceArcCutoff_core
      rw [abs_mul,abs_of_pos hap]
      have hh := (le_div_iff₀ (show 0<2*a by positivity)).mp hx
      nlinarith
    have hsx : sourceArcCutoffScale s x=1 := sourceArcCutoffScale_core s
      (hx.trans (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hscale (by norm_num))))
    change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale s x)-
      annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoff (a*x))‖≤_
    rw [hc,hsx,sub_self,norm_zero]
    positivity
  · have hout : (N : ℝ)^2/((2*a)*(N : ℝ)^2)≤|x| := by
      have he : (N : ℝ)^2/((2*a)*(N : ℝ)^2)=1/(2*a) := by field_simp
      rw [he]
      exact (lt_of_not_ge hx).le
    have hm := annularOscillatoryModel_outside_arc hN hβ0 hβ1
      (show 0<2*a by positivity) (sq_pos_of_pos hNr) hout
    have hb : |sourceArcCutoffScale s x-sourceArcCutoff (a*x)|≤1 := by
      change |sourceArcCutoff ((16 : ℝ)^s*x)-sourceArcCutoff (a*x)|≤1
      apply abs_le.mpr
      constructor <;> linarith [sourceArcCutoff_nonneg ((16 : ℝ)^s*x),
        sourceArcCutoff_nonneg (a*x),sourceArcCutoff_le_one ((16 : ℝ)^s*x),sourceArcCutoff_le_one (a*x)]
    change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale s x)-
      annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoff (a*x))‖≤_
    rw [←mul_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_one _)).trans
      (hm.trans_eq (by ring))

theorem circle_annular_common_source_difference {N s : ℕ} (hN : 2≤N)
    {β a : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (ha : 2≤a) (hscale : (16 : ℝ)^s≤a) (r : ℚ) :
    ‖circleAnnularSource N (by omega) β s r-circleWidthAnnular N (by omega) β a ha r‖≤
      12*a/(Real.pi*(N : ℝ)^2) := by
  let f := localizedAnnularSource N (by omega) β s-annularCutoffSymbol N (by omega) β a
  have hf : ∀ x,1≤|x| → f x=0 := by
    intro x hx
    simp only [f,ContinuousMap.sub_apply,localizedAnnularSource_support N (by omega) β s x hx,
      annularCutoffSymbol_support N (by omega) β ha x hx,sub_self]
  apply (ContinuousMap.norm_le _ (by positivity : 0≤12*a/(Real.pi*(N : ℝ)^2))).mpr
  intro ξ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) (ξ-((r : ℝ) : PrimeCircle)) : ℝ)
  have hb := compactCircleLift_norm_bound f hf (annular_common_source_difference hN hβ0 hβ1 ha hscale)
    (ξ-((r : ℝ) : PrimeCircle))
  change ‖compactPeriodWindow f x‖≤_ at hb
  change ‖compactPeriodWindow (localizedAnnularSource N (by omega) β s) x-
    compactPeriodWindow (annularCutoffSymbol N (by omega) β a) x‖≤_
  have he : compactPeriodWindow f x=compactPeriodWindow (localizedAnnularSource N (by omega) β s) x-
      compactPeriodWindow (annularCutoffSymbol N (by omega) β a) x := by
    simp only [f,compactPeriodWindow,ContinuousMap.sub_apply]
    ring
  rw [he] at hb
  exact hb.trans_eq (by ring)

theorem weighted_common_source_difference {N : ℕ} (hN : 2≤N) (Γ : Finset ℚ)
    {β a A : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1) (ha : 2≤a) (hA : 0≤A)
    (hscale : ∀ r∈Γ,(16 : ℝ)^(Nat.log2 r.den)≤a)
    (c : ℚ → ℂ) (hc : ∀ r∈Γ,‖c r‖≤A) :
    ‖varyingIndexAnnularBlock Γ N (by omega) β c-
      weightedWidthAnnularBlock Γ N (by omega) β a ha c‖≤
        (Γ.card : ℝ)*A*(12*a)/(Real.pi*(N : ℝ)^2) := by
  unfold varyingIndexAnnularBlock weightedWidthAnnularBlock
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ r∈Γ,‖c r • circleAnnularSource N (by omega) β (Nat.log2 r.den) r-
        c r • circleWidthAnnular N (by omega) β a ha r‖ := norm_sum_le _ _
    _ = ∑ r∈Γ,‖c r‖*‖circleAnnularSource N (by omega) β (Nat.log2 r.den) r-
        circleWidthAnnular N (by omega) β a ha r‖ := by
      apply sum_congr rfl
      intro r _
      have he : c r • circleAnnularSource N (by omega) β (Nat.log2 r.den) r-
          c r • circleWidthAnnular N (by omega) β a ha r=
          c r • (circleAnnularSource N (by omega) β (Nat.log2 r.den) r-
            circleWidthAnnular N (by omega) β a ha r) := by
        ext θ
        simp only [ContinuousMap.smul_apply,ContinuousMap.sub_apply,smul_eq_mul]
        ring
      rw [he,norm_smul]
    _ ≤ ∑ _r∈Γ,A*(12*a/(Real.pi*(N : ℝ)^2)) :=
      sum_le_sum (fun r hr => mul_le_mul (hc r hr)
        (circle_annular_common_source_difference hN hβ0 hβ1 ha (hscale r hr) r) (norm_nonneg _) hA)
    _ = _ := by rw [sum_const,nsmul_eq_mul];ring

theorem common_source_difference_maximum {M : ℕ} (hM : 2≤M) (Γ : Finset ℚ)
    {a A : ℝ} (ha : 2≤a) (hA : 0≤A) (hscale : ∀ r∈Γ,(16 : ℝ)^(Nat.log2 r.den)≤a)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ r∈Γ,‖c r‖≤A) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier
        (varyingIndexAnnularBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c-
        weightedWidthAnnularBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a ha c) f x‖≤g x) ∧
      ‖g‖≤(24*(Γ.card : ℝ)*A*a/(Real.pi*(M : ℝ)^2))*‖f‖ := by
  let m := fun j => varyingIndexAnnularBlock Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c-
      weightedWidthAnnularBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) a ha c
  let b := (Γ.card : ℝ)*A*(12*a)/(Real.pi*(M : ℝ)^2)
  have hb : 0≤b := by dsimp [b];positivity
  have hm (j : ℕ) (ξ : PrimeCircle) : ‖m j ξ‖≤b*(1/4 : ℝ)^j := by
    have hn := (ContinuousMap.norm_coe_le_norm (m j) ξ).trans
      (weighted_common_source_difference (dyadic_annular_scale_lower hM j) Γ (hβ0 j) (hβ1 j) ha hA hscale c hc)
    have he : ((((2 : ℕ)^j*M : ℕ) : ℝ)^2)=(4 : ℝ)^j*(M : ℝ)^2 := by
      push_cast
      rw [mul_pow,←pow_mul,Nat.mul_comm j 2,pow_mul]
      norm_num
    apply hn.trans_eq
    dsimp [b]
    rw [he,show (1/4 : ℝ)^j=1/(4 : ℝ)^j from one_div_pow _ _]
    ring
  obtain ⟨g,hg,ht,hn⟩ := geometric_symbol_maximum m hb hm f
  refine ⟨g,hg,ht,?_⟩
  exact hn.trans_eq (by dsimp [b];ring)

end PrimeSquares
