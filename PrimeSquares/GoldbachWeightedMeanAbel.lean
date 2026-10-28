import PrimeSquares.GoldbachWeightedAbel
import PrimeSquares.GoldbachWeightedKernels
import PrimeSquares.GoldbachWeightedMeanValue

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_mean_abel (R M c a b A : ℝ) (n : ℤ)
    (ha : 2≤a) (hab : a≤b) (hA : 0≤A)
    (hL : ∀ t∈Set.Icc a b,2≤M-Real.log c-Real.log t)
    (hmean : ∀ t∈Set.Icc a b,
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤A*t/Real.sqrt (Real.log t)) :
    (∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,
      goldbachWeightedMultiplicative R n u/((u:ℝ)*(M-Real.log c-Real.log u)^2))≤
      A*(∫ t in Set.Ioc a b,1/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2))+
        A/(Real.sqrt (Real.log a)*(M-Real.log c-Real.log a)^2) := by
  let f := goldbachWeightedLogKernel M c
  let f' := fun t : ℝ=>(2-(M-Real.log c-Real.log t))/(t^2*(M-Real.log c-Real.log t)^3)
  let H := goldbachWeightedCountingModel A
  let H' := fun t : ℝ=>A/Real.sqrt (Real.log t)-A/(2*(Real.sqrt (Real.log t))^3)
  have hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t := by
    intro t ht
    exact goldbach_weighted_log_kernel_deriv M c t (by linarith [ht.1]) (by linarith [hL t ht])
  have hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t :=
    fun t ht=>goldbach_weighted_counting_model_deriv A t (by linarith [ht.1])
  have hfi : IntegrableOn f' (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have hL0 : M-Real.log c-Real.log t≠0 := by linarith [hL t ht]
    have hden : t^2*(M-Real.log c-Real.log t)^3≠0 := mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 3 hL0)
    apply ContinuousAt.continuousWithinAt
    dsimp only [f']
    fun_prop
  have hHc : ContinuousOn H' (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have hlog : 0<Real.log t := Real.log_pos (by linarith [ht.1])
    have hs : Real.sqrt (Real.log t)≠0 := (Real.sqrt_pos.mpr hlog).ne'
    have hden : 2*(Real.sqrt (Real.log t))^3≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hs)
    apply ContinuousAt.continuousWithinAt
    dsimp only [H']
    fun_prop
  have hnonneg (t : ℝ) (ht : t∈Set.Icc a b) : 0≤f t ∧ f' t≤0 :=
    goldbach_weighted_log_kernel_sign M c t (by linarith [ht.1]) (hL t ht)
  have hb := goldbach_abel_decreasing_upper (goldbachWeightedMultiplicative R n)
    (by linarith : 0≤a) hab f f' H H' hf hH hfi hHc.intervalIntegrable
    (hnonneg a ⟨le_rfl,hab⟩).1 (hnonneg b ⟨hab,le_rfl⟩).1
    (sum_nonneg (fun u _=>goldbach_weighted_multiplicative_nonneg R n u))
    (fun t ht=>(hnonneg t ht).2) hmean
  have hsum : (∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,f u*goldbachWeightedMultiplicative R n u)=
      ∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,goldbachWeightedMultiplicative R n u/
        ((u:ℝ)*(M-Real.log c-Real.log u)^2) := by
    apply sum_congr rfl
    intro u _
    dsimp only [f,goldbachWeightedLogKernel]
    ring
  have hfcont : ContinuousOn f (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht=>(hf t ht).continuousAt.continuousWithinAt
  have huppercont : ContinuousOn (fun t : ℝ=>A/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2))
      (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have hL0 : M-Real.log c-Real.log t≠0 := by linarith [hL t ht]
    have hlog : 0<Real.log t := Real.log_pos (by linarith [ht.1])
    have hs : Real.sqrt (Real.log t)≠0 := (Real.sqrt_pos.mpr hlog).ne'
    have hden : t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2≠0 :=
      mul_ne_zero (mul_ne_zero ht0 hs) (pow_ne_zero 2 hL0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hint : (∫ t in Set.Ioc a b,f t*H' t)≤
      A*(∫ t in Set.Ioc a b,1/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2)) := by
    rw [←integral_const_mul]
    have hleft : IntegrableOn (fun t=>f t*H' t) (Set.Ioc a b) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (hfcont.mul hHc).intervalIntegrable
    have hright : IntegrableOn (fun t : ℝ=>A/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2)) (Set.Ioc a b) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp huppercont.intervalIntegrable
    have hri : IntegrableOn (fun t : ℝ=>A*(1/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2)))
        (Set.Ioc a b) volume := hright.congr_fun (fun t _=>by dsimp only;ring) measurableSet_Ioc
    apply integral_mono_ae hleft hri
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hh := mul_le_mul_of_nonneg_left
      (goldbach_weighted_counting_model_deriv_le A t hA (by linarith [ht.1]))
      (hnonneg t ⟨ht.1.le,ht.2⟩).1
    dsimp only [f,H',goldbachWeightedLogKernel] at hh ⊢
    simp only [div_eq_mul_inv,mul_inv_rev] at hh ⊢
    convert hh using 1;ring
  have ha0 : a≠0 := by linarith
  have hlog := Real.log_pos (show 1<a by linarith)
  have hs := (Real.sqrt_pos.mpr hlog).ne'
  have hL0 : M-Real.log c-Real.log a≠0 := by linarith [hL a ⟨le_rfl,hab⟩]
  have hboundary : f a*H a=A/(Real.sqrt (Real.log a)*(M-Real.log c-Real.log a)^2) := by
    dsimp only [f,H,goldbachWeightedLogKernel,goldbachWeightedCountingModel]
    field_simp
  rw [hsum,hboundary] at hb
  linarith only [hb,hint]

noncomputable def goldbachWeightedMeanAmplitude (K δ K₁ R : ℝ) (n : ℤ) (ε : ℝ) : ℝ :=
  (goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/Real.log R)*
    (goldbachWeightedC R n/goldbachWeightedB R n)/Real.sqrt (Real.log R)

theorem goldbach_weighted_mean_abel_effective (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁) :
    ∃ K δ : ℝ,0<K ∧ 0<δ ∧ ∀ R : ℝ,3≤R→∀ n : ℤ,∀ M c a b ε : ℝ,
      Real.exp 16<a→a≤b→1/Real.sqrt (Real.log a)<ε→ε≤1/2→R≤a^ε→
      6*Real.log R+10*K₀≤ε^2*Real.log a→
      (∀ t∈Set.Icc a b,2≤M-Real.log c-Real.log t)→
      (∑ u∈Ioc ⌊a⌋₊ ⌊b⌋₊,goldbachWeightedMultiplicative R n u/
        ((u:ℝ)*(M-Real.log c-Real.log u)^2))≤
        goldbachWeightedMeanAmplitude K δ K₁ R n ε*
          (∫ t in Set.Ioc a b,1/(t*Real.sqrt (Real.log t)*(M-Real.log c-Real.log t)^2))+
        goldbachWeightedMeanAmplitude K δ K₁ R n ε/
          (Real.sqrt (Real.log a)*(M-Real.log c-Real.log a)^2) := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := goldbach_weighted_mean_normalized hT K₀ K₁ hK₀ hK₁ hM hV
  refine ⟨K,δ,hK,hδ,?_⟩
  intro R hR n M c a b ε ha hab hε hεB hRa hbudget hL
  have hexp : (17:ℝ)≤Real.exp 16 := by have hh := Real.add_one_le_exp (16:ℝ);linarith
  have ha2 : 2≤a := by linarith
  have hloga : 0<Real.log a := Real.log_pos (by linarith)
  have hlogR : 0<Real.log R := Real.log_pos (by linarith)
  have hε0 : 0<ε := (one_div_pos.mpr (Real.sqrt_pos.mpr hloga)).trans hε
  let A := goldbachWeightedMeanAmplitude K δ K₁ R n ε
  have hA : 0≤A := by
    have hC := goldbach_weighted_C_positive R (by linarith) n
    have hB := goldbach_weighted_B_positive R (by linarith) n
    have hc := goldbach_half_mean_constant_positive
    dsimp only [A,goldbachWeightedMeanAmplitude]
    positivity
  apply goldbach_weighted_mean_abel R M c a b A n ha2 hab hA hL
  intro t ht
  have hat : a≤t := ht.1
  have hlogt : Real.log a≤Real.log t := Real.log_le_log (by linarith) hat
  have hεt : 1/Real.sqrt (Real.log t)<ε :=
    (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hloga) (Real.sqrt_le_sqrt hlogt)).trans_lt hε
  have hRt : R≤t^ε := hRa.trans (Real.rpow_le_rpow (by linarith : 0≤a) hat hε0.le)
  have hbudgett : 6*Real.log R+10*K₀≤ε^2*Real.log t :=
    hbudget.trans (mul_le_mul_of_nonneg_left hlogt (sq_nonneg ε))
  have hh := hbound R hR n t ε (ha.trans_le hat) hεt hεB hRt hbudgett
  have hsum : goldbachRealSummatory (goldbachWeightedMultiplicative R n) t=
      ∑ u∈range (⌊t⌋₊+1),goldbachWeightedMultiplicative R n u := by
    rw [goldbachRealSummatory,Nat.range_succ_eq_Icc_zero]
  rw [hsum]
  apply hh.trans_eq
  dsimp only [A,goldbachWeightedMeanAmplitude]
  ring

end PrimeSquares
