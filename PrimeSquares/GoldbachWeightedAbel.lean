import PrimeSquares.GoldbachCountingPartialSummation

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachRealSummatory (c : ℕ→ℝ) (t : ℝ) : ℝ :=
  ∑ k∈Icc 0 ⌊t⌋₊,c k

theorem goldbach_abel_model_identity (c : ℕ→ℝ) {a b : ℝ} (ha : 0≤a) (hab : a≤b)
    (f f' H H' : ℝ→ℝ)
    (hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t)
    (hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t)
    (hfi : IntegrableOn f' (Set.Icc a b)) (hHi : IntervalIntegrable H' volume a b) :
    (∑ k∈Ioc ⌊a⌋₊ ⌊b⌋₊,f k*c k)-(∫ t in Set.Ioc a b,f t*H' t)=
      f b*(goldbachRealSummatory c b-H b)-f a*(goldbachRealSummatory c a-H a)-
        ∫ t in Set.Ioc a b,f' t*(goldbachRealSummatory c t-H t) := by
  have hderiv : Set.EqOn f' (deriv f) (Set.Icc a b) := fun t ht=>(hf t ht).deriv.symm
  have hdi := hfi.congr_fun hderiv measurableSet_Icc
  have habelf := sum_mul_eq_sub_sub_integral_mul c ha hab (fun t ht=>(hf t ht).differentiableAt) hdi
  have he : (∫ t in Set.Ioc a b,deriv f t*∑ k∈Icc 0 ⌊t⌋₊,c k)=
      ∫ t in Set.Ioc a b,f' t*goldbachRealSummatory c t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hf t ⟨ht.1.le,ht.2⟩).deriv]
    rfl
  rw [he] at habelf
  have hfii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi
  have hHc : ContinuousOn H (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht=>(hH t ht).continuousAt.continuousWithinAt
  have hmulH : IntegrableOn (fun t=>f' t*H t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfii.mul_continuousOn hHc)
  have hmulA : IntegrableOn (fun t=>f' t*goldbachRealSummatory c t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c (m:=0) ha hfi).mono_set Set.Ioc_subset_Icc_self
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht=>hf t (by simpa only [Set.uIcc_of_le hab] using ht))
    (fun t ht=>hH t (by simpa only [Set.uIcc_of_le hab] using ht)) hfii hHi
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab] at hparts
  have hdiff : (∫ t in Set.Ioc a b,f' t*(goldbachRealSummatory c t-H t))=
      (∫ t in Set.Ioc a b,f' t*goldbachRealSummatory c t)-∫ t in Set.Ioc a b,f' t*H t := by
    simp_rw [mul_sub]
    exact integral_sub hmulA hmulH
  rw [habelf,hparts,hdiff]
  unfold goldbachRealSummatory
  ring

theorem goldbach_abel_decreasing_upper (c : ℕ→ℝ) {a b : ℝ} (ha : 0≤a) (hab : a≤b)
    (f f' H H' : ℝ→ℝ)
    (hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t)
    (hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t)
    (hfi : IntegrableOn f' (Set.Icc a b)) (hHi : IntervalIntegrable H' volume a b)
    (hfa : 0≤f a) (hfb : 0≤f b) (hA0 : 0≤goldbachRealSummatory c a)
    (hmono : ∀ t∈Set.Icc a b,f' t≤0)
    (hbound : ∀ t∈Set.Icc a b,goldbachRealSummatory c t≤H t) :
    (∑ k∈Ioc ⌊a⌋₊ ⌊b⌋₊,f k*c k)≤
      (∫ t in Set.Ioc a b,f t*H' t)+f a*H a := by
  have hfii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi
  have hHc : ContinuousOn H (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht=>(hH t ht).continuousAt.continuousWithinAt
  have hAH : IntegrableOn (fun t=>f' t*(goldbachRealSummatory c t-H t)) (Set.Ioc a b) := by
    simp_rw [mul_sub]
    exact ((integrableOn_mul_sum_Icc c (m:=0) ha hfi).mono_set Set.Ioc_subset_Icc_self).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfii.mul_continuousOn hHc))
  have hnonneg : 0≤∫ t in Set.Ioc a b,f' t*(goldbachRealSummatory c t-H t) := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact mul_nonneg_of_nonpos_of_nonpos (hmono t ⟨ht.1.le,ht.2⟩)
      (sub_nonpos.mpr (hbound t ⟨ht.1.le,ht.2⟩))
  have he := goldbach_abel_model_identity c ha hab f f' H H' hf hH hfi hHi
  have hb := mul_nonpos_of_nonneg_of_nonpos hfb (sub_nonpos.mpr (hbound b ⟨hab,le_rfl⟩))
  have h₀ := mul_nonneg hfa hA0
  nlinarith only [he,hnonneg,hb,h₀]

theorem goldbach_abel_increasing_error (c : ℕ→ℝ) {a b B : ℝ}
    (ha : 0≤a) (hab : a≤b) (_hB : 0≤B) (f f' H H' : ℝ→ℝ)
    (hf : ∀ t∈Set.Icc a b,HasDerivAt f (f' t) t)
    (hH : ∀ t∈Set.Icc a b,HasDerivAt H (H' t) t)
    (hfi : IntegrableOn f' (Set.Icc a b)) (hHi : IntervalIntegrable H' volume a b)
    (hfa : 0≤f a) (hfb : 0≤f b)
    (hmono : ∀ t∈Set.Icc a b,0≤f' t)
    (hbound : ∀ t∈Set.Icc a b,|goldbachRealSummatory c t-H t|≤B) :
    (∑ k∈Ioc ⌊a⌋₊ ⌊b⌋₊,f k*c k)≤
      (∫ t in Set.Ioc a b,f t*H' t)+2*B*f b := by
  have hfii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi
  have hHc : ContinuousOn H (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht=>(hH t ht).continuousAt.continuousWithinAt
  have hAH : IntegrableOn (fun t=>f' t*(goldbachRealSummatory c t-H t)) (Set.Ioc a b) := by
    simp_rw [mul_sub]
    exact ((integrableOn_mul_sum_Icc c (m:=0) ha hfi).mono_set Set.Ioc_subset_Icc_self).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfii.mul_continuousOn hHc))
  have hint : -B*(∫ t in Set.Ioc a b,f' t)≤
      ∫ t in Set.Ioc a b,f' t*(goldbachRealSummatory c t-H t) := by
    rw [←integral_const_mul]
    apply integral_mono_ae ((hfi.mono_set Set.Ioc_subset_Icc_self).const_mul (-B)) hAH
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hh := (abs_le.mp (hbound t ⟨ht.1.le,ht.2⟩)).1
    nlinarith only [mul_le_mul_of_nonneg_left hh (hmono t ⟨ht.1.le,ht.2⟩)]
  have hFTC : (∫ t in Set.Ioc a b,f' t)=f b-f a := by
    rw [←intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht=>hf t (by simpa only [Set.uIcc_of_le hab] using ht)) hfii
  have he := goldbach_abel_model_identity c ha hab f f' H H' hf hH hfi hHi
  have hb := mul_le_mul_of_nonneg_left (abs_le.mp (hbound b ⟨hab,le_rfl⟩)).2 hfb
  have h₀ := mul_le_mul_of_nonneg_left (abs_le.mp (hbound a ⟨le_rfl,hab⟩)).1 hfa
  rw [hFTC] at hint
  nlinarith only [he,hint,hb,h₀]

end PrimeSquares
