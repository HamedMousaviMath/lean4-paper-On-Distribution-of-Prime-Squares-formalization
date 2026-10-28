import PrimeSquares.GoldbachWeightedMeanAbel
import PrimeSquares.GoldbachWeightedHarmonic

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_mean_coarse (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁) :
    ∃ D A : ℝ,1<D ∧ 0<A ∧ ∀ R : ℝ,Real.exp 2≤R→∀ n : ℤ,∀ x : ℝ,R^D≤x→
      (∑ u∈range (⌊x⌋₊+1),goldbachWeightedMultiplicative R n u)≤
        A*(goldbachWeightedC R n/goldbachWeightedB R n)*x/
          (Real.sqrt (Real.log R)*Real.sqrt (Real.log x)) := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := goldbach_weighted_mean_normalized hT K₀ K₁ hK₀ hK₁ hM hV
  let D := 100+100*K₀
  let A := (goldbachHalfMeanConstant+K)*(1+K₁)
  have hD : 100≤D := by dsimp only [D];linarith
  have hA : 0<A := by
    have hh := goldbach_half_mean_constant_positive
    dsimp only [A]
    positivity
  refine ⟨D,A,by linarith,hA,?_⟩
  intro R hR n x hRx
  have hexp : (3:ℝ)≤Real.exp 2 := by have hh := Real.add_one_le_exp (2:ℝ);linarith
  have hR3 : 3≤R := hexp.trans hR
  have hR0 : 0<R := by linarith
  have hlogR : 2≤Real.log R := by
    have hh := Real.log_le_log (Real.exp_pos 2) hR
    rwa [Real.log_exp] at hh
  have hx0 : 0<x := (Real.rpow_pos_of_pos hR0 D).trans_le hRx
  have hlogx : D*Real.log R≤Real.log x := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hR0 D) hRx
    rwa [Real.log_rpow hR0] at hh
  have hbiglog : (200:ℝ)≤Real.log x := by
    have hh := mul_le_mul hD hlogR (by norm_num : (0:ℝ)≤2) (by linarith : 0≤D)
    nlinarith only [hh,hlogx]
  have hxexp : Real.exp 16<x := by
    have hh := Real.exp_lt_exp.mpr (show (16:ℝ)<Real.log x by linarith)
    rwa [Real.exp_log hx0] at hh
  have hε : 1/Real.sqrt (Real.log x)<(1/2:ℝ) := by
    have hs : (2:ℝ)<Real.sqrt (Real.log x) := Real.lt_sqrt_of_sq_lt (by nlinarith)
    apply (div_lt_iff₀ (show 0<Real.sqrt (Real.log x) by linarith)).mpr
    linarith
  have hRε : R≤x^(1/2:ℝ) := by
    apply (Real.log_le_log_iff hR0 (Real.rpow_pos_of_pos hx0 (1/2))).mp
    rw [Real.log_rpow hx0]
    have hh := mul_le_mul_of_nonneg_right (show (2:ℝ)≤D by linarith) (show 0≤Real.log R by linarith)
    nlinarith only [hh,hlogx]
  have hbudget : 6*Real.log R+10*K₀≤(1/2:ℝ)^2*Real.log x := by
    have hh := mul_nonneg hK₀ (show 0≤Real.log R-2 by linarith)
    dsimp only [D] at hlogx
    nlinarith only [hlogx,hh,hlogR,hK₀]
  have hb := hbound R hR3 n x (1/2) hxexp hε le_rfl hRε hbudget
  have heps : (1/2:ℝ)^δ≤1 := Real.rpow_le_one (by norm_num) (by norm_num) hδ.le
  have hfirst : goldbachHalfMeanConstant+K*(1/2:ℝ)^δ≤goldbachHalfMeanConstant+K := by
    nlinarith only [mul_le_mul_of_nonneg_left heps hK.le]
  have hsecond : 1+K₁/Real.log R≤1+K₁ := by
    have hh := div_le_self hK₁ (show 1≤Real.log R by linarith)
    linarith
  have hfac : (goldbachHalfMeanConstant+K*(1/2:ℝ)^δ)*(1+K₁/Real.log R)≤A := by
    have hc := goldbach_half_mean_constant_positive
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hratio : 0≤(goldbachWeightedC R n/goldbachWeightedB R n)*x/
      (Real.sqrt (Real.log R)*Real.sqrt (Real.log x)) := by
    have hC := goldbach_weighted_C_positive R (by linarith) n
    have hB := goldbach_weighted_B_positive R (by linarith) n
    positivity
  have hh := mul_le_mul_of_nonneg_right hfac hratio
  apply hb.trans
  convert hh using 1 <;> ring

theorem goldbach_weighted_prime_reciprocal (K z b : ℝ) (hM : ClassicalPrimeLogMertens K)
    (hz : 2≤z) (hb : z≤b) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime ∧ z≤(p:ℝ) ∧ (p:ℝ)≤b) :
    (∑ p∈P,1/(p:ℝ))≤(Real.log b+K)/Real.log z := by
  have hlogz : 0<Real.log z := Real.log_pos (by linarith)
  have hsubset : P⊆goldbachPrimeCutoff b := by
    intro p hp
    exact (mem_goldbachPrimeCutoff (by linarith) p).mpr ⟨(hP p hp).1,(hP p hp).2.2⟩
  have hpoint : ∀ p∈P,1/(p:ℝ)≤(Real.log p/(p:ℝ))/Real.log z := by
    intro p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hP p hp).1.pos
    have hlog := Real.log_le_log (by linarith : 0<z) (hP p hp).2.1
    apply (le_div_iff₀ hlogz).mpr
    convert div_le_div_of_nonneg_right hlog hp0.le using 1;ring
  have hs : (∑ p∈P,Real.log p/(p:ℝ))≤∑ p∈goldbachPrimeCutoff b,Real.log p/(p:ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hpP
    have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _)
  have hall := (abs_le.mp (hM.all b (by linarith))).2
  calc
    _≤∑ p∈P,(Real.log p/(p:ℝ))/Real.log z := sum_le_sum hpoint
    _=(∑ p∈P,Real.log p/(p:ℝ))/Real.log z := (sum_div _ _ _).symm
    _≤(Real.log b+K)/Real.log z := div_le_div_of_nonneg_right (by linarith) hlogz.le

theorem goldbach_harmonic_tail_linear (c : ℕ→ℝ) (a b A : ℝ)
    (ha : 2≤a) (hab : a≤b) (hA : 0≤A) (hc : ∀ u,0≤c u)
    (hmean : ∀ t∈Set.Icc a b,goldbachRealSummatory c t≤A*t) :
    (∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,c u/(u:ℝ))≤A*(1+Real.log b) := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  let f := fun t : ℝ=>1/t
  let f' := fun t : ℝ=> -(1/t^2)
  let H := fun t : ℝ=>A*t
  let H' := fun _ : ℝ=>A
  have hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    convert (hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id t) ht0 using 1
    · rfl
    · dsimp only [f',id_eq]
      ring
  have hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t := by
    intro t ht
    simpa only [H,H',id_eq,mul_one] using (hasDerivAt_id t).const_mul A
  have hfi : IntegrableOn f' (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht2 : t^2≠0 := pow_ne_zero 2 ht0
    dsimp only [f']
    fun_prop
  have hHi : IntervalIntegrable H' volume a b := intervalIntegrable_const
  have hh := goldbach_abel_decreasing_upper c ha0.le hab f f' H H' hf hH hfi hHi
    (by dsimp only [f];positivity) (by dsimp only [f];positivity)
    (sum_nonneg (fun u _=>hc u))
    (fun t _=>neg_nonpos.mpr (by positivity)) hmean
  have hi : (∫ t in Set.Ioc a b,1/t)=Real.log b-Real.log a := by
    rw [←intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      simpa only [one_div] using Real.hasDerivAt_log (show t≠0 by linarith [ht.1])
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : t≠0 := by linarith [ht.1]
      fun_prop
  have he : (∫ t in Set.Ioc a b,f t*H' t)=A*(Real.log b-Real.log a) := by
    dsimp only [f,H']
    simp_rw [mul_comm (1/_) A]
    rw [integral_const_mul,hi]
  have hbdy : f a*H a=A := by dsimp only [f,H];field_simp
  rw [he,hbdy] at hh
  have hsum : (∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,f u*c u)=∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,c u/(u:ℝ) := by
    apply sum_congr rfl
    intro u _
    dsimp only [f]
    ring
  rw [hsum] at hh
  have hl : 0≤Real.log a := Real.log_nonneg (by linarith)
  nlinarith only [hh,mul_nonneg hA hl]

theorem goldbach_weighted_harmonic_refined (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ K₂ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) :
    ∃ D A : ℝ,1<D ∧ 0<A ∧ ∀ R : ℝ,Real.exp 2≤R→∀ n : ℤ,∀ b : ℝ,R^D≤b→
      (∑ u∈Icc 1 ⌊b⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))≤
        3*((1+K₂/Real.log 2)*(Real.log (R^D+1)/Real.log 2)^2)^3+
          A*(goldbachWeightedC R n/goldbachWeightedB R n)/Real.log R*(1+Real.log b) := by
  obtain ⟨D,A,hD,hA,hbound⟩ := goldbach_weighted_mean_coarse hT K₀ K₁ hK₀ hK₁ hM hV
  refine ⟨D,A,hD,hA,?_⟩
  intro R hR n b hDb
  have hR1 : 1<R := by
    have hh := Real.add_one_le_exp (2:ℝ)
    linarith
  have hR0 : 0<R := by linarith
  have hlogR : 0<Real.log R := Real.log_pos hR1
  have hRd : R≤R^D := by
    conv_lhs => rw [←Real.rpow_one R]
    exact Real.rpow_le_rpow_of_exponent_le hR1.le hD.le
  have hd2 : 2≤R^D := by
    have hh := Real.add_one_le_exp (2:ℝ)
    linarith
  let B := A*(goldbachWeightedC R n/goldbachWeightedB R n)/Real.log R
  have hratio : 0≤A*(goldbachWeightedC R n/goldbachWeightedB R n) := by
    have hC := goldbach_weighted_C_positive R (by linarith) n
    have hB := goldbach_weighted_B_positive R (by linarith) n
    positivity
  have hB : 0≤B := div_nonneg hratio hlogR.le
  have hmean : ∀ t∈Set.Icc (R^D) b,
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤B*t := by
    intro t ht
    have ht0 : 0<t := by linarith [ht.1]
    have hlogs : Real.log R≤Real.log t := Real.log_le_log hR0 (hRd.trans ht.1)
    have hs : Real.log R≤Real.sqrt (Real.log R)*Real.sqrt (Real.log t) := by
      have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogs) (Real.sqrt_nonneg (Real.log R))
      rwa [←pow_two,Real.sq_sqrt hlogR.le] at hh
    have hh := div_le_div_of_nonneg_left (mul_nonneg hratio ht0.le) hlogR hs
    rw [goldbachRealSummatory,←Nat.range_succ_eq_Icc_zero]
    apply (hbound R hR n t ht.1).trans
    convert hh using 1; dsimp only [B]; ring
  have htail := goldbach_harmonic_tail_linear (goldbachWeightedMultiplicative R n) (R^D) b B
    hd2 hDb hB (goldbach_weighted_multiplicative_nonneg R n) hmean
  have hprefix := goldbach_weighted_harmonic_uniform R n K₂ (R^D) hK₂ hd2 hI
  have hfloor : ⌊R^D⌋₊≤⌊b⌋₊ := Nat.floor_mono hDb
  have hpos : 1≤⌊R^D⌋₊ := (Nat.le_floor_iff (by linarith : (0:ℝ)≤R^D)).mpr (by exact_mod_cast (show (1:ℝ)≤R^D by linarith))
  have he : (Icc 1 ⌊R^D⌋₊)∪(Ioc ⌊R^D⌋₊ ⌊b⌋₊)=Icc 1 ⌊b⌋₊ := by
    ext u
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hdj : Disjoint (Icc 1 ⌊R^D⌋₊) (Ioc ⌊R^D⌋₊ ⌊b⌋₊) := by
    apply disjoint_left.mpr
    intro u hu hv
    simp only [mem_Icc,mem_Ioc] at hu hv
    omega
  rw [←he,sum_union hdj]
  exact add_le_add hprefix htail

end PrimeSquares
