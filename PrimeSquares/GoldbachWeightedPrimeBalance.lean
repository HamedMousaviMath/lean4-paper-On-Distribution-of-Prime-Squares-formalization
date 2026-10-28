import PrimeSquares.GoldbachWeightedMeanValue
import PrimeSquares.GoldbachWeightedAbel
import PrimeSquares.GoldbachWeightedKernels

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachThreeLogCoefficient (p : ℕ) : ℝ :=
  if p.Prime ∧ p%4=3 then Real.log p/(p:ℝ) else 0

theorem goldbach_three_prime_log_partition (x : ℝ) (hx : 2≤x) :
    (∑ p∈goldbachPrimeCutoff x,Real.log p/(p:ℝ))=
      Real.log 2/2+
      (∑ p∈(goldbachPrimeCutoff x).filter (fun p : ℕ=>p%4=1),Real.log p/(p:ℝ))+
      ∑ p∈(goldbachPrimeCutoff x).filter (fun p : ℕ=>p%4=3),Real.log p/(p:ℝ) := by
  classical
  let P := goldbachPrimeCutoff x
  have h2 : 2∈P := (mem_goldbachPrimeCutoff (by linarith) 2).mpr ⟨by decide,hx⟩
  have he : P.erase 2=P.filter (fun p : ℕ=>p%4=1)∪P.filter (fun p : ℕ=>p%4=3) := by
    ext p
    simp only [mem_erase,mem_union,mem_filter]
    constructor
    · rintro ⟨hp2,hp⟩
      have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
      have hodd := hprime.eq_two_or_odd
      by_cases h4 : p%4=1
      · exact Or.inl ⟨hp,h4⟩
      · exact Or.inr ⟨hp,by omega⟩
    · rintro (⟨hp,h4⟩|⟨hp,h4⟩) <;> exact ⟨by omega,hp⟩
  have hd : Disjoint (P.filter (fun p : ℕ=>p%4=1)) (P.filter (fun p : ℕ=>p%4=3)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have := (mem_filter.mp hp).2
    have := (mem_filter.mp hq).2
    omega
  change (∑ p∈P,Real.log p/(p:ℝ))=_
  rw [←add_sum_erase P (fun p : ℕ=>Real.log p/(p:ℝ)) h2,he,sum_union hd]
  norm_num only [Nat.cast_ofNat]
  ring

theorem goldbach_three_log_summatory (x : ℝ) :
    goldbachRealSummatory goldbachThreeLogCoefficient x=
      ∑ p∈(goldbachPrimeCutoff x).filter (fun p : ℕ=>p%4=3),Real.log p/(p:ℝ) := by
  classical
  simp only [goldbachRealSummatory,goldbachPrimeCutoff,filter_filter,sum_filter,
    Nat.range_succ_eq_Icc_zero,goldbachThreeLogCoefficient]

theorem goldbach_three_log_mertens (K : ℝ) (_hK : 0≤K) (hM : ClassicalPrimeLogMertens K)
    (x : ℝ) (hx : 2≤x) :
    |goldbachRealSummatory goldbachThreeLogCoefficient x-Real.log x/2|≤2*K+1 := by
  have he := goldbach_three_prime_log_partition x hx
  have hA := abs_le.mp (hM.all x hx)
  have hB := abs_le.mp (hM.one x hx)
  have hlog0 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  rw [goldbach_three_log_summatory]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem goldbach_weighted_prime_abel (K M c a b : ℝ) (hK : 0≤K)
    (hM : ClassicalPrimeLogMertens K) (ha : 2≤a) (hab : a≤b)
    (hL : ∀ t∈Set.Icc a b,0<M-Real.log c-Real.log t ∧
      M-Real.log c-Real.log t≤2*Real.log t) :
    (∑ p∈(Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p : ℕ=>p.Prime ∧ p%4=3),
      1/((p:ℝ)*(M-Real.log c-Real.log p)^2))≤
      (1/2:ℝ)*(∫ t in Set.Ioc a b,1/(t*Real.log t*(M-Real.log c-Real.log t)^2))+
        2*(2*K+1)*goldbachWeightedPrimeKernel M c b := by
  classical
  let f := goldbachWeightedPrimeKernel M c
  let f' := fun t : ℝ=>(2*Real.log t-(M-Real.log c-Real.log t))/
    (t*(Real.log t)^2*(M-Real.log c-Real.log t)^3)
  let H := fun t : ℝ=>Real.log t/2
  let H' := fun t : ℝ=>(1/2:ℝ)/t
  have hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t := by
    intro t ht
    exact goldbach_weighted_prime_kernel_deriv M c t (by linarith [ht.1]) (hL t ht).1.ne'
  have hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    convert (Real.hasDerivAt_log ht0).div_const 2 using 1
    dsimp only [H']
    ring
  have hfi : IntegrableOn f' (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have hl0 : Real.log t≠0 := (Real.log_pos (by linarith [ht.1] : 1<t)).ne'
    have hL0 := (hL t ht).1.ne'
    have hden : t*(Real.log t)^2*(M-Real.log c-Real.log t)^3≠0 :=
      mul_ne_zero (mul_ne_zero ht0 (pow_ne_zero 2 hl0)) (pow_ne_zero 3 hL0)
    apply ContinuousAt.continuousWithinAt
    dsimp only [f']
    fun_prop
  have hHi : IntervalIntegrable H' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    dsimp only [H']
    fun_prop
  have hnonneg (t : ℝ) (ht : t∈Set.Icc a b) : 0≤f t ∧ 0≤f' t :=
    goldbach_weighted_prime_kernel_sign M c t (by linarith [ht.1]) (hL t ht).1 (hL t ht).2
  have hb := goldbach_abel_increasing_error goldbachThreeLogCoefficient (by linarith : 0≤a)
    hab (by linarith : 0≤2*K+1) f f' H H' hf hH hfi hHi
    (hnonneg a ⟨le_rfl,hab⟩).1 (hnonneg b ⟨hab,le_rfl⟩).1
    (fun t ht=>(hnonneg t ht).2)
    (fun t ht=>goldbach_three_log_mertens K hK hM t (by linarith [ht.1]))
  have hsum : (∑ p∈Ioc ⌊a⌋₊ ⌊b⌋₊,f p*goldbachThreeLogCoefficient p)=
      ∑ p∈(Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p : ℕ=>p.Prime ∧ p%4=3),
        1/((p:ℝ)*(M-Real.log c-Real.log p)^2) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases h : p.Prime ∧ p%4=3
    · rw [goldbachThreeLogCoefficient,ite_eq_left h,ite_eq_left h]
      have hp0 : (0:ℝ)<p := by exact_mod_cast h.1.pos
      have hlog : Real.log p≠0 := (Real.log_pos (by exact_mod_cast h.1.one_lt)).ne'
      have hpa : a<(p:ℝ) := (Nat.floor_lt (by linarith : 0≤a)).mp (mem_Ioc.mp hp).1
      have hpbN : (p:ℝ)≤(⌊b⌋₊:ℕ) := by exact_mod_cast (mem_Ioc.mp hp).2
      have hpb : (p:ℝ)≤b := hpbN.trans (Nat.floor_le (by linarith : 0≤b))
      have hL0 := (hL p ⟨hpa.le,hpb⟩).1.ne'
      dsimp only [f,goldbachWeightedPrimeKernel]
      field_simp
    · simp only [goldbachThreeLogCoefficient,ite_eq_right h,mul_zero]
  have hint : (∫ t in Set.Ioc a b,f t*H' t)=
      (1/2:ℝ)*(∫ t in Set.Ioc a b,1/(t*Real.log t*(M-Real.log c-Real.log t)^2)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [f,H',goldbachWeightedPrimeKernel]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rwa [hsum,hint] at hb

end PrimeSquares
